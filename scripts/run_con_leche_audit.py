#!/usr/bin/env python3
"""Run a provenance-bound ConLeche audit without shell command interpolation."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone


CANONICAL_MODULES = (
    "StrongPerimetralTurning",
    "Cycle2",
    "ConstitutiveAlignment",
)
HEX_COMMIT = re.compile(r"^[0-9a-f]{40}$")
ACCEPTED = re.compile(r"^con-leche: accepted ([0-9]+) declarations \(--verified\)$")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def run_text(arguments: list[str], cwd: Path) -> str:
    completed = subprocess.run(
        arguments,
        cwd=cwd,
        check=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return completed.stdout.rstrip()


def run_logged(arguments: list[str], cwd: Path, log: Path) -> None:
    with log.open("wb") as output:
        completed = subprocess.run(
            arguments,
            cwd=cwd,
            check=False,
            stdout=output,
            stderr=subprocess.STDOUT,
        )
    if completed.returncode != 0:
        raise RuntimeError(
            f"command failed with exit {completed.returncode}; see {log}"
        )


def verify_manifest(repository: Path) -> None:
    manifest = repository / "MANIFEST.sha256"
    for line_number, raw_line in enumerate(
        manifest.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if not raw_line:
            continue
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", raw_line)
        if match is None:
            raise RuntimeError(f"malformed manifest line {line_number}")
        expected, relative = match.groups()
        target = (repository / relative).resolve()
        try:
            target.relative_to(repository)
        except ValueError as error:
            raise RuntimeError(f"manifest path escapes repository: {relative}") from error
        if not target.is_file():
            raise RuntimeError(f"manifest file is missing: {relative}")
        if sha256(target) != expected:
            raise RuntimeError(f"manifest mismatch: {relative}")


def require_external_output(repository: Path, output: Path) -> None:
    try:
        output.relative_to(repository)
    except ValueError:
        return
    raise RuntimeError("the audit workspace must be outside the repository")


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Export the canonical Lean roots and run ConLeche verified mode."
    )
    parser.add_argument("--lean4export", type=Path, required=True)
    parser.add_argument("--lean4export-source", type=Path, required=True)
    parser.add_argument("--lean4export-commit", required=True)
    parser.add_argument("--con-leche", type=Path, required=True)
    parser.add_argument("--con-leche-source", type=Path, required=True)
    parser.add_argument("--con-leche-commit", required=True)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--confirmatory", action="store_true")
    parser.add_argument("--expected-head")
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    repository = Path(__file__).resolve().parent.parent
    exporter = arguments.lean4export.resolve()
    checker = arguments.con_leche.resolve()
    exporter_source = arguments.lean4export_source.resolve()
    checker_source = arguments.con_leche_source.resolve()
    for label, path in (("lean4export", exporter), ("ConLeche", checker)):
        if not path.is_file():
            raise RuntimeError(f"{label} executable not found: {path}")
    for label, commit in (
        ("lean4export", arguments.lean4export_commit),
        ("ConLeche", arguments.con_leche_commit),
    ):
        if HEX_COMMIT.fullmatch(commit) is None:
            raise RuntimeError(f"{label} commit must be a full lowercase Git hash")

    for label, source, binary, expected_commit in (
        ("lean4export", exporter_source, exporter, arguments.lean4export_commit),
        ("ConLeche", checker_source, checker, arguments.con_leche_commit),
    ):
        if not (source / ".git").exists():
            raise RuntimeError(f"{label} source is not a Git checkout: {source}")
        source_head = run_text(["git", "rev-parse", "HEAD"], source)
        if source_head != expected_commit:
            raise RuntimeError(
                f"{label} source HEAD is {source_head}, expected {expected_commit}"
            )
        try:
            binary.relative_to(source)
        except ValueError as error:
            raise RuntimeError(
                f"{label} binary is not inside its declared source checkout"
            ) from error

    checker_source_status = run_text(
        ["git", "status", "--porcelain", "--untracked-files=all"], checker_source
    )
    if checker_source_status:
        raise RuntimeError("ConLeche source checkout must be clean")
    exporter_source_status = run_text(
        ["git", "status", "--porcelain", "--untracked-files=all"], exporter_source
    )
    exporter_toolchain_override = exporter_source_status == " M lean-toolchain"
    if exporter_source_status and not exporter_toolchain_override:
        raise RuntimeError(
            "lean4export source must be clean or differ only by the project "
            "lean-toolchain override"
        )
    if exporter_toolchain_override:
        project_toolchain = (repository / "lean-toolchain").read_bytes()
        exporter_toolchain = (exporter_source / "lean-toolchain").read_bytes()
        if project_toolchain != exporter_toolchain:
            raise RuntimeError(
                "lean4export toolchain override differs from the project toolchain"
            )

    head = run_text(["git", "rev-parse", "HEAD"], repository)
    status = run_text(
        ["git", "status", "--porcelain", "--untracked-files=all"], repository
    )
    if arguments.confirmatory:
        if arguments.expected_head is None:
            raise RuntimeError("--confirmatory requires --expected-head")
        if HEX_COMMIT.fullmatch(arguments.expected_head) is None:
            raise RuntimeError("--expected-head must be a full lowercase Git hash")
        if head != arguments.expected_head:
            raise RuntimeError(f"HEAD is {head}, expected {arguments.expected_head}")
        if status:
            raise RuntimeError("confirmatory audit requires a clean Git tree")

    if arguments.output_dir is None:
        output = Path(
            tempfile.mkdtemp(prefix="structural-foundations-con-leche-")
        ).resolve()
    else:
        output = arguments.output_dir.resolve()
        require_external_output(repository, output)
        output.mkdir(parents=True, exist_ok=True)

    mode = "confirmatory" if arguments.confirmatory else "exploratory"
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    stem = f"con-leche-{mode}-{head[:12]}-{stamp}"
    build_log = output / f"{stem}.lake-build.log"
    export_path = output / f"{stem}.ndjson"
    export_stderr = output / f"{stem}.lean4export.stderr.log"
    checker_stdout = output / f"{stem}.con-leche.stdout.log"
    checker_stderr = output / f"{stem}.con-leche.stderr.log"
    report_path = output / f"{stem}.report.txt"
    artifacts = (
        build_log,
        export_path,
        export_stderr,
        checker_stdout,
        checker_stderr,
        report_path,
        output / f"{stem}.lake-clean.log",
    )
    existing = [str(path) for path in artifacts if path.exists()]
    if existing:
        raise RuntimeError("refusing to overwrite audit artifacts: " + ", ".join(existing))

    exporter_hash_before = sha256(exporter)
    checker_hash_before = sha256(checker)

    if arguments.confirmatory:
        run_logged(["lake", "clean"], repository, output / f"{stem}.lake-clean.log")
    run_logged(["lake", "build"], repository, build_log)
    verify_manifest(repository)

    export_command = [
        "lake",
        "env",
        str(exporter),
        *CANONICAL_MODULES,
    ]
    with export_path.open("wb") as exported, export_stderr.open("wb") as errors:
        export_run = subprocess.run(
            export_command,
            cwd=repository,
            check=False,
            stdout=exported,
            stderr=errors,
        )
    if export_run.returncode != 0:
        raise RuntimeError(
            f"lean4export failed with exit {export_run.returncode}; see {export_stderr}"
        )

    export_hash_before = sha256(export_path)
    checker_command = [str(checker), "--verified", "--jobs=1", str(export_path)]
    with checker_stdout.open("wb") as output_stream, checker_stderr.open("wb") as errors:
        checker_run = subprocess.run(
            checker_command,
            cwd=repository,
            check=False,
            stdout=output_stream,
            stderr=errors,
        )
    export_hash_after = sha256(export_path)
    if export_hash_before != export_hash_after:
        raise RuntimeError("the export changed between hashing and checker completion")

    stdout_text = checker_stdout.read_text(encoding="utf-8", errors="replace").strip()
    accepted_match = ACCEPTED.fullmatch(stdout_text)
    if checker_run.returncode != 0 or accepted_match is None:
        raise RuntimeError(
            "ConLeche did not produce a theorem-covered acceptance; "
            f"exit={checker_run.returncode}, stdout={stdout_text!r}, "
            f"stderr={checker_stderr}"
        )

    exporter_hash_after = sha256(exporter)
    checker_hash_after = sha256(checker)
    if exporter_hash_before != exporter_hash_after:
        raise RuntimeError("lean4export binary changed during the audit")
    if checker_hash_before != checker_hash_after:
        raise RuntimeError("ConLeche binary changed during the audit")

    head_after = run_text(["git", "rev-parse", "HEAD"], repository)
    status_after = run_text(
        ["git", "status", "--porcelain", "--untracked-files=all"], repository
    )
    if head_after != head:
        raise RuntimeError("repository HEAD changed during the audit")
    if status_after != status:
        raise RuntimeError("repository working-tree state changed during the audit")
    verify_manifest(repository)

    lean_version = run_text(["lake", "env", "lean", "--version"], repository)
    report_lines = [
        "CON_LECHE_CONSTITUTIVE_AUDIT_V1",
        f"status={mode}",
        f"timestamp_utc={datetime.now(timezone.utc).isoformat()}",
        f"repository_commit={head}",
        f"repository_clean_at_start={str(not bool(status)).lower()}",
        f"repository_clean_at_end={str(not bool(status_after)).lower()}",
        f"lean_version={lean_version}",
        f"modules={' '.join(CANONICAL_MODULES)}",
        f"lean4export_commit={arguments.lean4export_commit}",
        f"lean4export_source={exporter_source}",
        f"lean4export_source_status={exporter_source_status or 'clean'}",
        f"lean4export_toolchain_override={str(exporter_toolchain_override).lower()}",
        f"lean4export_binary={exporter}",
        f"lean4export_binary_sha256_before={exporter_hash_before}",
        f"lean4export_binary_sha256_after={exporter_hash_after}",
        f"con_leche_commit={arguments.con_leche_commit}",
        f"con_leche_source={checker_source}",
        f"con_leche_source_status={checker_source_status or 'clean'}",
        f"con_leche_binary={checker}",
        f"con_leche_binary_sha256_before={checker_hash_before}",
        f"con_leche_binary_sha256_after={checker_hash_after}",
        f"export_command={' '.join(export_command)}",
        f"export_path={export_path}",
        f"export_bytes={export_path.stat().st_size}",
        f"export_sha256_before={export_hash_before}",
        f"export_sha256_after={export_hash_after}",
        f"checker_command={' '.join(checker_command)}",
        "checker_mode=verified",
        "checker_jobs=1",
        f"checker_exit_code={checker_run.returncode}",
        f"accepted_declarations={accepted_match.group(1)}",
        f"checker_stdout={stdout_text}",
        f"build_log={build_log}",
        f"export_stderr_log={export_stderr}",
        f"checker_stderr_log={checker_stderr}",
    ]
    report_path.write_text("\n".join(report_lines) + "\n", encoding="utf-8")
    print(report_path)
    print(f"report_sha256={sha256(report_path)}")
    print(stdout_text)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"audit failed: {error}", file=sys.stderr)
        raise SystemExit(1)
