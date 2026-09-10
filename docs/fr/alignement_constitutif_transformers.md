# Architecture neuronale constitutive pour l’alignement relatif

*Mémoire causale, succession et réalisation par transformer*

[English](../en/constitutive_transformer_alignment.md) | **Français**

Navigation : [synthèse structurelle](fondements_structurels.md) ·
[méthode](methode_roles_constitutifs_relationnels.md) ·
[Cycle 1 — alignement relatif](alignement_relatif.md) ·
[Cycle 2 — alignement réflexif](alignement_reflexif.md)

## 1. Thèse

Une architecture neuronale constitutive ne reçoit pas ses objets comme des
unités déjà individuées auxquelles elle ajouterait ensuite mémoire, contrôle et
évaluation. Elle construit des occurrences dont l’identité dépend de leur
formation, de leurs rôles relationnels et de leur participation à une histoire.
Ses supports numériques réalisent ces occurrences ; ils ne les définissent pas
à eux seuls.

L’hypothèse architecturale est :

> **Une machine neuronale peut conserver une identité, raisonner par succession
> et localiser une rupture normative si elle transporte fidèlement les relations
> qui constituent ses occurrences, sépare régime et norme, et rend toute
> effectuation dépendante d’un certificat portant sur l’action exacte.**

Le transformer intervient comme une réalisation possible du plan neuronal. Il
n’est ni le principe d’individuation, ni la norme, ni le régime d’admission. La
mémoire persistante, le raisonnement à horizon long et le diagnostic des
hallucinations relatives sont trois applications d’une même architecture de
constitution, de conservation et de sortie.

Cette thèse ne dépend pas d’une promesse empirique. Le dépôt fournit déjà son
socle structurel ; les contrats et instances propres à la machine neuronale sont
construits en Lean, tandis que l’observation numérique finie et toute
généralisation à un réseau entraîné restent identifiées séparément.

## 2. Résultats formels de départ

Le Cycle 1 vérifie en Lean une chaîne où construction, réalisation, régime et
norme restent distincts :

```text
présentation
→ histoire dépendamment typée
→ occurrences individuées par leur formation
→ rôles et accords exacts
→ réalisation fidèle
→ régime opérationnel
→ norme autonome
→ adéquation exacte sur les mêmes histoires
→ continuation positive minimale
→ sortie localisée du régime et de la norme
```

Les principaux points d’ancrage sont :

| Fonction | Identifiants Lean |
| --- | --- |
| réalisation exacte et rôle résiduel | `ExactInternalRealization`, `FaithfulExtension` |
| sortie abstraite d’un régime | `RegimeExit`, `UniformRegimeExit` |
| histoire générée depuis une racine | `RootedGeneratedHistory` |
| adéquation entre régime et norme | `NormativeAdequacy`, `AdequateAlong` |
| régime circulaire | `CircularRefinement` |
| norme circulaire autonome | `CircularSpecificationSatisfaction` |
| soundness | `circularRefinement_soundSpecification` |
| complétude | `circularSpecification_complete` |
| continuation minimale | `oneStepAfterPerimeter` |
| sortie relative à la norme | `oneStepSpecRelativeHistoryExit` |

`CircularRefinement P H` et `CircularSpecificationSatisfaction P H` sont des
types de témoins. Le dépôt construit une transformation dans chaque direction.
Au niveau propositionnel, leur habitabilité est donc équivalente :

```text
Nonempty (CircularRefinement P H)
↔
Nonempty (CircularSpecificationSatisfaction P H)
```

Cette adéquation n’interdit pas la continuation de la construction.
`oneStepAfterPerimeter` est formé positivement, possède une réalisation fidèle
et sort du régime ainsi que de la norme sur la même continuation.

Le Cycle 2 élève ensuite l’adéquation au niveau des statuts représentés :

```text
représentation exacte de statuts déterminés
+ statut diagonal extérieur au régime de représentation
→ absence de clôture réflexive globale
```

Les identifiants correspondants sont `Represents`,
`InternallyRepresentable`, `PullbackStatus`, `transportRepresentation`,
`diagonalStatus_notRepresentable` et `noGlobalReflectiveClosure`.

## 3. Conséquence architecturale de la non-clôture

La non-clôture ne retire rien à l’exactitude déjà construite. Elle interdit de
transformer une représentation exacte de statuts déterminés en prétention à une
représentation interne totale de tous les statuts de la machine.

L’architecture recherchée est donc dynamique, relative et localement
déterminée :

```text
un régime déterminé
↔ une norme autonome sur les mêmes objets
→ exactitude dans cette portée
+ possibilité d’un statut extérieur
→ succession ou sortie explicite, jamais clôture globale postulée
```

La machine ne se certifie pas globalement. Elle transporte des témoins dans une
portée déclarée, représente exactement certains statuts, et conserve une sortie
positive lorsqu’une frontière opérationnelle, normative ou représentationnelle
est atteinte.

Cette conséquence motive l’architecture qui suit. Elle ne remplace pas ses
contrats : chaque transport, admission, effectuation et succession doit encore
être construit.

## 4. Machine constitutive abstraite

La machine fondamentale est indépendante de tout choix neuronal :

```lean
State : Type
Step  : State → State → Type
```

Une histoire est une composition proof-relevant de pas. Une occurrence est
indexée par l’histoire qui l’a formée. Elle conserve au minimum :

- son pas de formation ;
- ses états source et cible ;
- sa position dans la trajectoire ;
- ses dépendances constitutives ;
- sa provenance ;
- les obligations auxquelles elle participe.

La même lecture peut donc correspondre à deux occurrences distinctes lorsque
leurs formations diffèrent. Inversement, deux supports matériels différents ne
réalisent une même occurrence que si une correspondance fidèle est construite.

Un rôle n’est pas une étiquette telle que `fact`, `memory` ou `error`. Il est
une exigence relationnelle dont dépend la participation d’une occurrence à la
construction. Un accord établit qu’une occurrence déterminée réalise
effectivement ce rôle :

```lean
Agreement
  (history : History)
  (role : Role)
  (occurrence : History.Occurrence history) : Type
```

Une réalisation exacte d’une famille de rôles fournit une application
injective vers les occurrences réalisées et un accord pour chaque rôle. Elle
n’exige pas que toute occurrence future ait déjà un rôle dans la famille
courante. Cette asymétrie permet la continuation sans effacer l’exactitude
locale.

## 5. Quatre plans et cinq distinctions

L’architecture sépare quatre plans :

```text
plan constitutif       formation, occurrences, rôles et histoires
plan formel-normatif   régime, norme, adéquation et preuves
plan opérationnel      actions, effets, mémoire et traces consommées
plan neuronal          activations, paramètres et propositions
```

Ces plans communiquent par des réalisations et des certificats explicites. Ils
ne sont pas identifiés.

Pour une histoire `H` et un candidat `x`, cinq familles doivent rester
distinctes :

```text
C(H, x)   construction interne de x
F(H, x)   réalisation fidèle de x
R(H, x)   admission de x par le régime
S(H, x)   satisfaction de la norme autonome
E(H, x)   effectuation gouvernée de l’action portée par x
```

L’alignement relatif est l’adéquation entre `R` et `S` sur les mêmes objets. Il
n’est ni un score, ni une préférence, ni une comparaison de sorties terminales.
L’effectuation est encore autre chose : elle détermine ce que le système peut
faire après admission.

Les séparations structurantes sont :

```text
construction          ≠ réalisation
réalisation           ≠ admission
admission             ≠ satisfaction normative
norme                 ≠ adéquation du régime
proposition           ≠ incorporation
apprentissage         ≠ succession constitutive
composition en trace  ≠ dépendance causale
causalité à un pas    ≠ autonomie multicycle
sortie opérationnelle ≠ sortie représentationnelle
```

## 6. Mémoire relative aux futurs pertinents

Une mémoire persistante n’est pas la conservation intégrale d’une histoire, ni
la disponibilité ultérieure d’un texte similaire. Elle conserve exactement les
différences nécessaires aux comportements futurs déclarés.

Une première interface constructive est :

```lean
Question : Type
Answer   : Question → Type
behaviour : State → (q : Question) → Answer q
encode    : State → Memory
```

Deux états sont équivalents relativement à ces questions lorsque :

```lean
FutureEquivalent left right :=
  ∀ q, behaviour left q = behaviour right q
```

Trois contrats doivent être distingués :

```text
solidité causale
  même mémoire → mêmes futurs pertinents

complétude relative
  mêmes futurs pertinents → même mémoire

exactitude relative
  même mémoire ↔ mêmes futurs pertinents
```

Une loi de mise à jour relie la transition réelle et la mémoire :

```text
encode (advance state) = update (encode state)
```

La famille de questions est explicite et extensible. Une fusion sûre dans une
famille présente ne devient pas automatiquement sûre sous toute question
future. L’architecture ne revendique donc ni mémoire universelle ni compression
irréversible sans contrat de stabilité supplémentaire.

## 7. Admission et effectuation normatives

Une action est définie avant son effet par sa nature, sa cible, ses paramètres,
son contexte constitutif, sa portée et l’effecteur demandé. Un certificat
d’autorisation est indexé par cette action exacte et ce contexte exact.

L’interface d’effectuation impose :

```text
effectuation(action, context)
→ admission(action, context)
```

Sous une adéquation normative démontrée :

```text
effectuation
→ admission par le régime
→ satisfaction de la norme autonome
```

Le certificat ne corrige pas le candidat. Il ne peut pas être transféré à une
autre cible, à une action modifiée ou à un autre contexte. Une voie d’effet qui
contourne cette interface invalide la garantie.

Trois diagnostics restent séparés :

```text
FormationFailure   le candidat ne peut être élaboré
RegimeExit         le candidat fidèle sort du régime
NormativeFailure   le candidat formé et réalisé est réfuté par la norme
```

Le diagnostic conserve le candidat et sa trace. Le confinement empêche un effet
gouverné lorsque le certificat normatif requis ne peut être construit ; il ne
prétend pas empêcher la formation interne du candidat.

## 8. Causalité constitutive de l’apprentissage à un pas

La cible n’est pas de placer apprentissage, prédiction et proposition dans une
même trace. Leur proximité chronologique ne démontre aucune dépendance causale.

Le contrat requis est :

```text
état prédictif parent
→ apprentissage effectif
→ état prédictif appris
→ prédiction apprise différente
→ prédiction consommée comme entrée constitutive
→ proposition constitutive différente
→ succession exacte
```

Il est vérifié par une paire de parcours contrôlés. Les deux parcours partagent :

- le même problème prédictif ;
- le même état constitutif ;
- le même producteur de proposition ;
- les mêmes paramètres de ce producteur ;
- le même aléa ;
- le même budget et les mêmes vues autorisées.

La seule variation initiale est l’état prédictif parent ou appris. Le témoin
doit ensuite établir :

1. que les prédictions diffèrent ;
2. que chaque prédiction est littéralement l’entrée constitutive consommée ;
3. que les propositions diffèrent ;
4. que la branche parent est rejetée pour un motif fixé ;
5. que la branche apprise construit la succession exacte ;
6. que le cas comparé a été choisi avant l’observation des résultats.

Cette chaîne respecte la distinction entre apprentissage et succession : le
premier cause une prédiction qui participe à la proposition suivante ; il ne se
confond pas avec l’incorporation ni avec le régime successeur.

`FreshProbeCausality.lean` ferme en amont l’acquisition de cette intervention.
Il sépare le corpus d’entraînement de la sonde d’évaluation, lie les deux par un
engagement unique, construit la réfutation de l’appartenance de la sonde au
corpus, puis exécute les états parent et appris sur la même vue autorisée de
cette sonde. L’état appris produit par cette procédure est exactement l’état de
poids fixe utilisé par la dynamique transformer à profondeur finie. Il s’agit
d’une instance finie construite, non de l’hypothèse que des poids entraînés
arbitraires satisfont ce contrat.

Le résultat à un pas est une condition nécessaire de la machine recherchée. À
lui seul, il ne démontre pas l’autonomie multicycle.

## 9. Succession constitutive et horizon long

Trois transitions sont formalisées séparément :

```text
apprentissage paramétrique : paramètres → paramètres
incorporation constitutive : état → état étendu
succession normative       : régime → régime successeur
```

Un cycle construit un candidat, sa réalisation, son diagnostic, une conséquence
autorisée, une incorporation éventuelle, l’état successeur et le régime
successeur. L’état successeur n’est jamais une donnée libre fournie après le
candidat.

L’itération exige un opérateur uniforme :

```text
cycle n
→ état effectivement produit
→ reconfiguration du problème suivant
→ cycle n + 1 consommant cet état exact
```

Deux reconstructions indépendantes, deux problèmes préparés séparément ou un
catalogue par profondeur ne constituent pas une itération. Pour établir le lien
intercycle, une ablation de l’état incorporé doit détruire ou modifier la
transition suivante conformément à une propriété préengagée.

`ReferenceModel.lean` ferme ces obligations dans une seule instance finie
intégrée. Les mêmes candidats et états raccordent les histoires pertinentes
pour les preuves, le régime et la norme définis indépendamment, la réalisation
fidèle, la mémoire exacte, l’action gouvernée, l’échec de formation, la paire
parent–appris contrôlée, les sorties opérationnelle et normative et la
non-clôture réflexive. Le candidat appris est exactement le candidat admis et
effectué ; le candidat parent est exactement la continuation fidèle rejetée par
le régime, la norme et l’effectuation gouvernée. Le modèle construit aussi deux
cycles avec le même opérateur et démontre que le second consomme la sortie du
premier après que la première mise à jour mémoire a reconfiguré son entrée.

L’horizon est ainsi structurel. Il mesure une composition conservée
d’occurrences, de dépendances et d’obligations, non un nombre de tokens. Une
séquence textuellement longue peut être structurellement rompue tôt ; une
séquence comprimée peut rester fidèle si les relations nécessaires sont
transportées.

`TransformerDynamics.lean` instancie la même discipline sur le cœur fini à
attention dure. Un opérateur uniforme s’exécute avec les mêmes poids appris,
incorpore la proposition produite comme relation suivante, puis s’exécute à
nouveau sur cette vue produite. Une ablation dédiée conserve tokens, cache,
mémoire, budget, cœur et poids, mais omet cette seule incorporation ; la seconde
prédiction et la seconde proposition changent alors. Cela établit une autonomie
finie de deux cycles dans le modèle déclaré.

`GovernedDynamics.lean` généralise ensuite cette dynamique à toute profondeur
finie `n : Nat` sans introduire de catalogue de cycles. `viewAt n` est produit
par le même opérateur ; `reachableTransformerAt n` porte l’histoire qui le
forme ; et `proposalIsNextConsumedRelation n` établit que la proposition du
rang `n` est exactement la relation consommée au rang `n + 1`.
`GovernedInvariant` agrège sur chaque état atteint la fidélité de la trajectoire,
l’exactitude et la conservation de la mémoire déclarée, l’adéquation
régime–norme, le statut normatif du candidat, sa conservation dans
l’élaboration et le confinement de son éventuel effet gouverné. Sa loi à un
pas est composée par `preservesAlongIteration`, ce qui construit l’invariant
pour tout horizon fini. Une ablation de la relation active modifie la
prédiction, la proposition et donc l’état successeur produit à chaque profondeur
de cette instance, tandis que l’arrêt borné reste un résultat constructif
explicite.

## 10. Réalisation neuronale

Le plan neuronal reçoit une vue autorisée de l’état. Cette vue exclut les
preuves, verdicts futurs, cibles exactes et sorties d’audit qui permettraient de
fabriquer le résultat attendu.

La chaîne de réalisation est :

```text
état latent
→ proposition discrète
→ élaboration totale
→ candidat accepté ou première erreur localisée
```

L’élaboration ne répare jamais la proposition. Les candidats invalides restent
représentables et auditables.

Une réalisation fidèle relie les occurrences constitutives aux objets
opérationnels effectivement consommés. Une similarité vectorielle, une réponse
finale correcte ou une reconstruction linguistique plausible ne suffit pas.
Les relations nécessaires doivent participer au calcul futur ; une structure
seulement journalisée n’est pas une réalisation causale.

La trace primaire lie :

```text
état appris
→ prédiction neuronale
→ entrée constitutive consommée
→ proposition discrète
→ candidat élaboré
```

Elle est scellée avant l’audit. L’auditeur vérifie après coup et ne choisit, ne
corrige, ne relance ni ne supprime aucune étape.

## 11. Réalisation par transformer

Le transformer est une instance du plan neuronal. Il peut proposer et
transporter des occurrences, dépendances, rôles, références de mémoire, actions
et prédictions de conséquences. Ses logits ne définissent ni l’identité, ni la
norme, ni l’admission.

Une première instance explicite :

- les tokens d’entrée ;
- les activations et paramètres ;
- l’état récurrent ou le cache ;
- la mémoire adressable ;
- la proposition discrète ;
- la trace de consommation ;
- la relation avec les occurrences formelles.

La paire causale parent–appris maintient invariant tout le contexte constitutif
et ne remplace que l’état prédictif. Elle doit produire deux prédictions et deux
propositions distinctes, puis le rejet précis de la branche parent et la
succession exacte de la branche apprise.

Les adresses techniques peuvent retrouver les occurrences, mais elles ne sont
pas leur identité. La computation doit rester équivariante sous renommage
cohérent des adresses.

L’instance finie ferme les obligations à un pas par une tête d’attention dure à
deux clés. Les tokens forment l’activation ; la relation forme avec elle la
requête ; l’attention sélectionne la valeur de mémoire effectivement utilisée
par la prédiction. La proposition apprise devient exactement la relation du
passage suivant, et son ablation modifie cette continuation. Un renommage
cohérent des deux clés, de leurs valeurs et de la requête conserve le résultat.
La proposition parent se décode en sortie opérationnelle du modèle de référence,
tandis que la proposition apprise se décode en son candidat admis, normatif et
associé à l’action gouvernée.

Cette fermeture porte sur une réalisation constructive finie d’attention dure.
Le module à un pas ne constitue pas isolément un résultat multicycle, mais sa
composition dans `TransformerDynamics.lean` puis `GovernedDynamics.lean`
construit respectivement deux cycles causalement liés et la dynamique gouvernée
à toute profondeur finie. Elle ne constitue ni un transformer entraîné, ni une
formalisation des tenseurs flottants de l’attention softmax, ni un résultat sur
un horizon infini.

Le modèle fini non neuronal précède cette instance. Il ferme les mêmes contrats
sur un domaine calculable et sert de référence de test hors ligne, jamais de
correcteur sur la voie causale du transformer.

## 12. Mémoire, rupture normative et hallucination relative

La mémoire persistante est démontrée dans une portée lorsque deux états fusionnés
par la mémoire sont indistinguables sous toutes les questions déclarées. Une
compression sans ce certificat reste une hypothèse d’implémentation.

La mémoire finie du transformer est exacte pour les deux requêtes de l’attention
dure et reste conservée par l’incorporation relationnelle. Son résumé retient
les deux valeurs nécessaires à ces futurs tout en excluant l’adresse technique
de focus.

Une hallucination relative peut être définie comme un candidat construit et
fidèlement réalisé dont la norme autonome est réfutée. Cette définition est
relative à la norme explicitement choisie. Elle ne transforme ni toute sortie
de régime ni toute erreur linguistique en hallucination.

Le témoin fini d’hallucination relative contient un seul et même candidat, son
histoire construite, sa réalisation injective fidèle, sa proposition rejetée
conservée et la réfutation de la norme autonome. Ce candidat est exactement la
sortie opérationnelle et normative, et l’action gouvernée correspondante ne
peut être effectuée. La construction interne demeure ; seul l’effet externe
certifié est confiné.

Le témoin recherché conserve sur le même candidat :

```text
formation positive
+ réalisation fidèle
+ structure antérieure préservée
+ première obligation normative réfutée
+ impossibilité de l’effet gouverné correspondant
```

Le système localise ainsi la rupture sans nier que la construction a continué.
La continuation rejetée reste disponible pour l’audit, tandis que l’effectuation
soumise au certificat est confinée.

## 13. Programme formel

Les nouveaux modules sont ordonnés par dépendance :

| Module | Obligation principale | Statut actuel |
| --- | --- | --- |
| `Machine.lean` | interface constitutive raccordée aux histoires du Cycle 1 | démontré |
| `CausalMemory.lean` | exactitude relative aux futurs déclarés et loi de mise à jour | démontré, avec séparateurs finis |
| `NormativeExecution.lean` | action, certificat et effectuation gouvernée | démontré, avec voie non médiée séparée |
| `NormativeFailure.lean` | diagnostics distincts sans dépendance neuronale | démontré |
| `Succession.lean` | itération uniforme, raccord normatif et arrêt explicite | démontré au niveau générique et fini |
| `LearningCausality.lean` | apprentissage causant la proposition suivante à un pas | démontré sur le contrat et une instance finie |
| `ReflectiveMachine.lean` | instance machine de la représentation exacte et de la non-clôture | démontré |
| `ReferenceModel.lean` | certificat fini intégré, des histoires et de l’adéquation jusqu’à la succession causale, l’action gouvernée, les cycles liés et la sortie réflexive | démontré |
| `NeuralRealization.lean` | contrat de fidélité neuronale et audit différé | défini et démontré sur une instance finie |
| `TransformerRealization.lean` | contrat transformer, attention dure, consommation de la relation proposée et intervention parent–appris | gate finie à un pas démontrée |
| `TransformerDynamics.lean` | mémoire exacte d’attention, rétroaction uniforme sur deux cycles, ablation intercycle, rupture normative relative et confinement | démontré sur l’instance finie à attention dure |
| `FreshProbeCausality.lean` | séparation engagée entre entraînement et sonde, fraîcheur constructive et emploi exact des poids acquis | démontré sur l’instance finie à attention dure |
| `GovernedDynamics.lean` | atteignabilité proof-relevant, invariant gouverné, transformations admissibles et dynamique transformer à profondeur finie arbitraire | démontré constructivement pour tout `n : Nat` |
| `ExecutableRefinement.lean` | frontière discrète canonique, raffinement exact, chaînage des traces et séparateurs négatifs | démontré constructivement pour tout `n : Nat` |
| `experiment/protocol_v1.py` | prototype numérique à attention softmax, séparation entraînement/sonde, traces immuables, contrôles et audit différé | source canonique corrigée ; run confirmatoire en attente de son commit de gel |

La façade `ConstitutiveAlignment.lean` importe les feuilles de ce graphe. Les
fichiers existants du Cycle 1 et du Cycle 2 restent l’autorité formelle ; les
nouveaux modules construisent des ponts et ne redéfinissent pas leurs résultats.

Chaque fichier Lean nouveau ou modifié doit rester constructif, sans `axiom`,
`sorry`, `Classical`, `propext` ni `Quot.sound`, et terminer par un bloc unique
`AXIOM_AUDIT`.

## 14. Ordre d’implémentation et gates

L’ordre de fermeture est :

```text
machine abstraite
→ mémoire et effectuation
→ succession et contrat causal générique
→ couche réflexive
→ modèle de référence fini
→ réalisation neuronale abstraite
→ instance transformer à un pas
→ dynamique transformer à deux cycles
→ invariant gouverné à toute profondeur finie
→ transformations admissibles et transport d’adéquation
→ raffinement de la frontière discrète exécutable
→ protocole expérimental reproductible
```

Le modèle fini doit comprendre deux occurrences de même lecture mais de
formations différentes, une mémoire qui les sépare par leurs futurs, un régime
et une norme indépendants, une paire parent–appris contrôlée, une branche
rejetée, une succession exacte et deux cycles dont le second dépend réellement
de l’état produit par le premier.

Le protocole numérique exige des sondes de smoke test et confirmatoire fixées,
toutes deux disjointes de l’ensemble d’entraînement et l’une de l’autre par
identifiant et par vue autorisée. Un smoke test n’exécute pas la sonde
confirmatoire. Le protocole vérifie aussi :

- absence de cible interdite dans la vue neuronale ;
- identité entre prédiction produite et entrée constitutive consommée ;
- différence de proposition sous intervention parent–appris sur cette même
  sonde ;
- consommation du véritable état successeur ;
- ablation du lien intercycle ;
- conservation des candidats invalides ;
- trace immuable et audit causalement silencieux ;
- contrôles, graines et critères fixés avant les runs confirmatoires.

Une gate échouée reste un résultat localisé. Elle ne peut être contournée par un
changement silencieux de protocole ou par une revendication plus faible laissée
implicite.

## 15. Statut exact

Le dépôt démontre actuellement :

- le noyau structurel dépendamment typé ;
- la sortie opérationnelle abstraite et concrète ;
- l’adéquation exacte du régime circulaire et de sa norme autonome ;
- la continuation minimale fidèlement réalisable qui sort des deux ;
- la représentation exacte de statuts déterminés ;
- le statut diagonal non représentable et la non-clôture réflexive globale ;
- une mémoire exacte relativement à des futurs déclarés, sa non-fusion et une
  loi autonome de mise à jour sur des modèles finis ;
- l’impossibilité de l’effectuation gouvernée sans certificat exact et le
  passage `effectuation → admission → norme` ;
- la séparation typée des échecs de formation, sorties de régime et ruptures
  normatives ;
- une itération uniforme consommant l’état réellement produit, la conservation
  d’obligations, un raccord explicite entre incorporation et succession
  normative, et un arrêt constructif ;
- un contrat causal à un pas reliant apprentissage, prédiction consommée,
  proposition différente, rejet parent et succession apprise ;
- un témoin d’acquisition sur sonde fraîche fixée dont le corpus et la sonde
  sont constructivement disjoints, dont l’engagement interdit la substitution
  de la sonde et dont les poids acquis sont exactement ceux de la dynamique à
  profondeur finie ;
- un modèle de référence fini intégré avec occurrences de même lecture mais de
  formations différentes, mémoire exacte, régime et norme indépendants,
  branches parent et apprise fidèles, action gouvernée, sorties distinctes,
  cycles liés et statut représenté avec diagonale extérieure ;
- une interface neuronale à quatre plans, une élaboration sans réparation, une
  fidélité sur la trajectoire et un audit différé causalement silencieux ;
- une interface de réalisation transformer et une instance finie d’attention
  dure où la proposition apprise est consommée comme relation suivante, la
  relation est active, le contrôle sans relation est inerte, le renommage des
  adresses conserve la prédiction et le raccord au modèle de référence est
  exact ;
- une dynamique transformer finie de deux cycles sous un opérateur uniforme et
  des poids appris fixes, avec rétroaction exacte de la proposition vers la
  relation, mémoire d’attention exacte, ablation intercycle dédiée et rupture
  normative relative confinée ;
- une dynamique transformer construite pour toute profondeur finie `n : Nat`,
  dont chaque état porte son histoire de formation et dont chaque proposition
  devient exactement la relation consommée au cycle suivant ;
- un invariant gouverné préservé sur tous ces états atteignables, réunissant
  sans les confondre fidélité, mémoire, adéquation, statut normatif,
  conservation de l’élaboration et confinement de l’effet ;
- un contrat de transformation admissible qui sépare apprentissage
  paramétrique, incorporation, mise à jour mémoire, transport de l’adéquation et
  transport injectif des actions et certificats ;
- une frontière exécutable discrète raffinant exactement la trace formelle à
  toute profondeur, avec rejet constructif d’un candidat réécrit, d’un effet
  forgé et d’un lien intercycle absent ; les statuts du certificat et de
  l’effectuation sont indexés par l’action exacte dérivée du candidat et par le
  contexte constitutif.

Séparément de ces théorèmes, le protocole numérique corrigé a passé un run non
confirmatoire sur sa sonde dédiée au smoke test. Son ensemble d’entraînement,
sa sonde de smoke test et sa sonde confirmatoire fixée sont disjoints deux à
deux, puis la comparaison parent–appris consomme la sonde sélectionnée sans
substitution. La sonde confirmatoire n’a pas été exécutée. Le JSON
confirmatoire, les rapports bilingues et le vérificateur en lecture seule
épinglé par empreintes ne seront produits qu’après le gel du script et de la
configuration dans un commit.
Jusque-là, aucune revendication numérique confirmatoire n’est formulée. Lean ne
lit pas le résultat JSON ; le théorème formel `TraceRefinement` et sa future
acceptation exécutable restent distincts.

Le dépôt ne démontre pas encore :

- une réalisation transformer entraînée à grande échelle ou une trajectoire
  effectivement infinie ;
- une réalisation fidèle par un réseau entraîné et ses tenseurs effectifs ;
- un résultat expérimental sur les hallucinations linguistiques.

Ces éléments restent des obligations ordonnées, pas des conclusions
anticipées. La frontière entre théorèmes Lean, contrats, implémentations et
observations demeure explicite.

## Conception

> **Déclaration de conception intellectuelle et de génération par IA.** Le
> responsable du projet déclare être à l’origine de l’essentiel des idées et de
> la direction de recherche du projet. Ce document a été écrit de A à Z par des
> modèles de la série ChatGPT d’OpenAI, sous direction humaine et au cours
> d’interactions successives. Voir la
> [déclaration bilingue complète](../../AI_AUTHORSHIP.md).
