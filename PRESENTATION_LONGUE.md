# Présentation longue

## Théorie constitutive de la détermination relationnelle

Cette théorie part d’un principe : **avant de représenter, mesurer, évaluer ou aligner un objet, il faut établir ce qui le constitue et ce qui permet de l’identifier à travers ses transformations.**

Elle prend pour objets centraux les **rôles constitutifs relationnels** : les déterminations structurelles établies pour des occurrences individuées à partir des relations qu’elles entretiennent au sein d’une construction.

L’ordre général de la théorie est le suivant :

```text
constitution
→ rôles constitutifs relationnels
→ dépendances
→ méthode de détermination
→ reconstruction
→ frontière constitutive
→ identité
→ persistance
→ alignement
```

La circularité joue dans ce cadre un rôle central, non comme fondement général de la théorie, mais comme **instance dans laquelle l’ensemble de cette architecture peut être déployé et éprouvé**.

---

## 1. Constitution

Le premier problème est :

> Qu’est-ce qui fait qu’un objet est cet objet dans une construction donnée ?

La réponse est relationnelle.

Une occurrence n’est pas d’abord déterminée par une valeur, une représentation ou une étiquette. Elle est individuée par sa formation et par les relations constitutives qu’elle entretient dans la construction : provenance, rapports de source et de cible, position, succession, composition et participation.

La constitution est donc première par rapport à la lecture, à la représentation et au statut.

```text
relations constitutives
        ↓
individuation de l’occurrence
        ↓
détermination constitutive
```

Cette priorité rend ensuite possible la question de l’identité : il faut d’abord établir **ce qui est déterminé** avant de pouvoir demander si cette détermination persiste.

---

## 2. Rôles constitutifs relationnels

Un **rôle constitutif relationnel** désigne la détermination structurelle établie pour une occurrence individuée à partir des relations qu’elle entretient et de la place qu’elle occupe dans une construction.

Le terme **constitutif** indique que ces relations interviennent dans ce qui permet de déterminer l’occurrence au sein de la construction.

Le terme **relationnel** indique que cette détermination ne se réduit ni à une propriété intrinsèque, ni à une étiquette, ni à une lecture ajoutée après coup.

La théorie vise à établir :

```text
occurrences individuées
        ↓
rôles constitutifs relationnels
        ↓
conditions de leur identité
        ↓
conditions de persistance
```

Déterminer un rôle constitutif relationnel exige également de distinguer les relations nécessaires à cette détermination des propriétés candidates dont il faut établir si elles doivent être posées comme primitives ou peuvent être dérivées d’une structure plus fondamentale.

Une propriété candidate ne doit donc pas être ajoutée simplement parce qu’elle est utile à une preuve. Il faut déterminer de quoi elle dépend.

```text
propriété candidate
        ↓
analyse de dépendance
        ↓
primitive
ou
reconstructible
```

Ces dépendances imposent un **ordonnancement de la construction**.

Si une détermination `B` dépend de `A`, alors `A` doit être établi avant `B`.

```text
A
↓
B
```

Ce qui dépend d’une détermination ne peut pas être utilisé rétroactivement pour constituer ce dont il dépend.

La théorie ne cherche donc pas à accumuler des propriétés, mais à établir **l’ordre réel des dépendances constitutives**.

---

## 3. Méthode de détermination des dépendances

Les rôles constitutifs relationnels sont des objets théoriques. La méthode sert à déterminer quelles structures sont réellement nécessaires pour les établir.

Le principe méthodologique est :

```text
affaiblir
→ séparer
→ reconstruire
```

On part d’une structure dans laquelle un résultat est démontrable.

On retire ensuite certaines données que l’on soupçonne de ne pas être primitives.

Si le résultat reste dérivable, ces données n’étaient pas nécessaires à ce niveau.

Si le résultat cesse d’être dérivable, on cherche un **modèle séparateur** qui conserve les propriétés déjà établies tout en faisant échouer la propriété candidate.

La méthode consiste alors à identifier les dépendances dont la nécessité peut être établie par séparation dans la classe de structures considérée.

```text
structure riche
        ↓ affaiblissement
structure plus faible
        ↓
résultat encore dérivable ?
     /              \
   oui              non
    ↓                ↓
dépendance        séparateur
inutile à          explicite
ce niveau             ↓
                  dépendance établie
                  par séparation
```

Les séparateurs établissent ainsi des non-implications précises et localisent les dépendances effectivement utilisées par les constructions formalisées. Ils ne prétendent pas établir une minimalité absolue parmi toutes les formalisations ou toutes les preuves possibles.

Enfin, lorsque des conditions supplémentaires sont réintroduites, on cherche à montrer que la structure plus riche peut être **reconstruite** à partir d’elles.

La distinction entre primitive et reconstructible n’est donc pas verbale. Elle est établie par des constructions positives, des séparateurs et des théorèmes de reconstruction.

Cette méthode permet notamment d’éviter deux erreurs opposées : supposer trop de structure dès le départ, ou prétendre dériver une propriété que les dépendances disponibles ne suffisent pas à déterminer.

---

## 4. La circularité comme instance centrale

La circularité constitue l’instance principale dans laquelle cette méthode peut être suivie depuis l’exactitude locale jusqu’à une frontière constitutive globale.

La chaîne générale est :

```text
exactitude locale minimale
        ↓
injectivité dérivée
        ↓
ordre et adjacence dérivés
        ↓
reconstruction du périmètre
        ↓
continuation positive
        ↓
séparation ancien / nouveau
        ↓
détermination résiduelle
        ↓
unicité de l’occurrence résiduelle
        ↓
interprétation de la frontière positive
        ↓
rejet de la totalisation
        ↓
classification exacte du régime
        ↓
maximalité relative du périmètre
```

### 4.1 Exactitude constitutive locale minimale

Le point de départ n’est pas une description globale complète du périmètre.

Une réalisation locale associe des occurrences aux exigences constitutives non fermantes et exige seulement un accord structurel exact sur leur adresse de source.

Cet accord minimal suffit ensuite à reconstruire davantage de structure.

```text
accord constitutif local exact
        ↓
état source exact
        ↓
état cible exact
        ↓
pas local exact
```

L’injectivité n’a donc pas besoin d’être postulée séparément dans cette situation.

Elle devient une conséquence de l’exactitude structurelle et de l’impossibilité pour deux profondeurs distinctes de partager le même parcours constitutif.

### 4.2 Ordre et adjacence dérivés

Dans une histoire véritablement générée, l’exactitude constitutive locale suffit également à reconstruire l’ordre entre les occurrences.

La précédence structurelle des exigences du périmètre est préservée.

L’adjacence canonique l’est également.

```text
exactitude constitutive locale
        ↓
injectivité
        ↓
précédence
        ↓
adjacence
```

Ces dépendances ne sont pas tautologiques.

Lorsqu’on affaiblit le carrier en abandonnant la structure globale d’histoire, on peut conserver une réalisation locale exacte et injective tout en permutant l’ordre des occurrences.

On peut également conserver l’ordre tout en intercalant des occurrences supplémentaires qui ne participent pas au pont constitutif requis.

Ces séparateurs montrent que :

```text
exactitude locale
≠ ordre automatique sur tout carrier

ordre positionnel
≠ participation constitutive
```

La reconstruction dépend donc de la structure véritablement disponible.

### 4.3 Reconstruction du périmètre

Lorsque les occurrences exactes vivent dans une véritable histoire générée, la structure locale peut être reconstruite globalement.

Les occurrences du périmètre permettent de factoriser récursivement l’histoire.

On obtient alors le **périmètre canonique reconstruit comme facteur initial** de l’histoire considérée.

```text
occurrences locales exactes
        ↓
factorisation structurelle
        ↓
périmètre canonique
reconstruit comme préfixe
de l’histoire
```

Il ne s’agit pas d’une reconstruction par comptage.

La profondeur numérique ou la longueur ne sont pas nécessaires à cette étape.

La reconstruction est d’abord constitutive et relationnelle.

L’expression **reconstruction exacte du périmètre** désigne ici l’exactitude de cette factorisation structurelle. Elle ne signifie pas que le périmètre serait défini par une longueur numérique exacte.

### 4.3.1 Fonction constitutive du périmètre reconstruit

Le périmètre reconstruit n’est pas recherché comme une mesure de taille ni comme une totalité de tout ce qui peut être construit.

Il fournit une **frontière structurelle canonique à l’intérieur de l’histoire**.

Cette frontière remplit plusieurs fonctions successives.

Elle délimite d’abord la partie de la construction dans laquelle les rôles internes ont déjà été réalisés.

Elle permet ensuite de distinguer les occurrences qui appartiennent à cette partie constituée des occurrences introduites par une continuation.

```text
histoire
=
périmètre reconstruit
+
continuation
```

Donc :

```text
occurrences du périmètre
        =
occurrences déjà constituées relativement
aux rôles internes

occurrences de la continuation
        =
occurrences nouvelles relativement
à cette constitution
```

Cette distinction est indispensable à la notion de résiduel.

Une occurrence ne peut être dite résiduelle que relativement à une structure dans laquelle les rôles internes ont déjà été déterminés et réalisés.

Le périmètre fournit précisément cette structure de référence.

Il remplit ensuite une deuxième fonction : il fournit le **représentant canonique relativement auquel le régime peut être classifié**.

Enfin, dans la théorie de la persistance, les occurrences de ce périmètre fournissent le carrier initial de l’instance circulaire à partir duquel les identités déjà constituées peuvent être suivies sous extension.

Ainsi :

```text
périmètre canonique reconstruit
        │
        ├─ délimite les rôles internes déjà réalisés
        │
        ├─ sépare ancien et nouveau
        │       ↓
        │   rend possible le résiduel
        │
        ├─ fournit le représentant canonique du régime
        │       ↓
        │   rend possible sa classification
        │
        └─ fournit les occurrences initiales
                ↓
            support de la persistance
```

Le périmètre joue donc une fonction charnière : **il transforme une collection d’accords locaux en une frontière structurelle à partir de laquelle peuvent être définis le nouveau, le résiduel, la maximalité du régime et la persistance des identités.**

La circularité fournit ainsi une fermeture relationnelle suffisante pour que l’interne soit délimité par un périmètre canonique. Cette fermeture ne constitue pourtant pas une totalisation de tout ce qui peut être construit. Le périmètre est complet relativement aux rôles internes déjà constitués, alors même que la génération peut se poursuivre au-delà de lui. C’est cet écart entre complétude constitutive et continuation possible qui rend possible l’apparition d’un résiduel et, ensuite, la détermination d’une frontière de régime.

### 4.4 Le périmètre n’arrête pas la génération

Une fois le périmètre canonique reconstruit, la construction libre peut encore continuer.

Il existe une continuation stricte au-delà du périmètre.

```text
périmètre canonique
        ↓
génération
        ↓
continuation stricte
```

Il ne faut donc pas parler d’un arrêt de la construction.

La distinction pertinente est entre :

```text
possibilité de continuer la construction
≠
possibilité de rester dans le même régime
```

C’est cette différence qui permet de définir une véritable frontière constitutive.

### 4.5 Détermination résiduelle

**Relativement au périmètre reconstruit**, la continuation introduit une partie nouvelle distincte des occurrences déjà présentes.

La distinction entre ancien et nouveau n’est donc pas ajoutée extérieurement : elle résulte de la factorisation structurelle de l’histoire en périmètre et continuation.

Lorsque cette séparation ancien / nouveau est équipée d’un marquage fidèle des rôles, une nouvelle occurrence ne peut pas réutiliser un rôle constitutif interne déjà attribué au périmètre.

```text
ancien
≠
nouveau

+
marquage fidèle
        ↓
impossibilité pour le nouveau
de réutiliser un rôle interne
        ↓
rôle résiduel
```

Une fois exclue, pour les nouvelles occurrences, la réutilisation des rôles internes, la contractilité du type de rôle résiduel force tout rôle résiduel obtenu à coïncider avec un même rôle distingué.

Le rôle résiduel n’est donc pas une étiquette ajoutée arbitrairement après la continuation. Il est obtenu par exclusion des rôles internes et détermination du seul rôle résiduel disponible.

### 4.6 Unicité de l’occurrence résiduelle

Le noyau de détermination résiduelle établit d’abord que toute nouvelle occurrence porte le même rôle résiduel distingué.

Lorsque le marquage des nouvelles occurrences est injectif, deux nouvelles occurrences portant ce même rôle ne peuvent pas rester distinctes.

```text
exclusion des rôles internes
+
contractilité du rôle résiduel
        ↓
même rôle résiduel
pour toute nouvelle occurrence
        ↓
fidélité du marquage
        ↓
une seule occurrence résiduelle
```

Une continuation positive possède donc une occurrence résiduelle distinguée et aucune autre occurrence nouvelle distincte.

Dans l’instance canonique à un pas, cette occurrence est précisément l’unique occurrence ajoutée au périmètre.

### 4.7 Du résiduel à la classification du régime

Le périmètre reconstruit fournit désormais le **référent canonique relativement auquel l’admission peut être classifiée**.

Le résiduel intervient directement dans le mécanisme qui permet cette classification.

Une extension positive fournit d’abord son noyau de détermination résiduelle.

Ce noyau produit une occurrence résiduelle unique.

Cette occurrence est ensuite utilisée pour construire l’interprétation de la frontière positive.

À partir de cette interprétation, une tentative de totalisation est formulée.

La tentative de totalisation cherche alors à absorber cette occurrence résiduelle dans une fermeture complète du régime. Dans l’instance circulaire, une telle absorption conduirait à contracter la différence constitutive que la construction a préservée.

L’obstruction constitutive déjà préservée permet de rejeter cette tentative.

```text
continuation positive
        ↓
noyau résiduel
        ↓
occurrence résiduelle unique
        ↓
interprétation de la frontière
        ↓
tentative de totalisation
        ↓
rejet par l’obstruction constitutive
```

Ce rejet élimine la branche positive d’un candidat admis.

Il permet alors d’obtenir la **classification exacte du régime** :

```text
candidat admis
        ↓
égalité avec le périmètre canonique
```

Réciproquement, le périmètre canonique possède un témoin d’admission.

On obtient ainsi :

```text
admission dans le régime
↔
égalité au périmètre canonique
```

### 4.8 Frontière constitutive et maximalité relative

La continuation libre au-delà du périmètre existe effectivement.

Mais puisqu’elle est strictement différente du périmètre canonique, la classification exacte du régime implique qu’elle ne peut pas être admise dans le même régime.

Plus généralement, aucune extension stricte du périmètre ne peut rester dans ce régime.

```text
périmètre canonique
        ↓
extension stricte possible
        ↓
sortie du régime
```

La notion correcte est donc celle de **frontière constitutive du régime** ou de **maximalité relative du périmètre**.

La construction continue.

Le régime, lui, ne se prolonge pas avec elle.

---

## 5. Longueur structurelle dérivée

La longueur intervient seulement après que la structure constitutive du périmètre et sa maximalité relative ont été établies.

La fonction constitutive du périmètre est donc déjà entièrement établie avant toute mesure numérique.

La longueur n’est pas un principe de constitution.

Elle mesure une construction déjà obtenue.

```text
constitution du périmètre
        ↓
classification / maximalité
        ↓
mesure de longueur
```

Une relation de préfixe constitutif implique une relation d’ordre sur les longueurs :

```text
A préfixe de B
        ↓
longueur(A) ≤ longueur(B)
```

Une extension stricte implique :

```text
A préfixe strict de B
        ↓
longueur(A) < longueur(B)
```

Les constructions partielles admissibles ne peuvent donc pas être plus longues que le périmètre.

Et toute construction appartenant au même régime circulaire possède exactement la longueur du périmètre canonique.

Mais cet ordre logique doit rester explicite :

> **L’égalité des longueurs n’est jamais utilisée pour identifier une histoire au périmètre canonique ; elle est obtenue après que cette identification a déjà été établie structurellement.**

Autrement dit :

```text
pas :
même longueur
→ même périmètre

mais :
même histoire constitutive que le périmètre
→ même longueur
```

La longueur est ainsi **dérivée de la structure constitutive**, et non utilisée pour la produire.

Cela inverse l’ordre explicatif habituel :

```text
pas :
longueur
→ périmètre

mais :
périmètre constitué
→ maximalité relative
→ longueur dérivée
```

---

Dans ce qui suit, les termes **identité**, **détermination constitutive** et **alignement** donnent une lecture théorique de structures et d’équations formelles explicites. Le développement Lean vérifie directement les occurrences, indexations, transports exacts, extensions, compositions et lois de naturalité qui contraignent cette lecture. Ces termes ne sont pas introduits comme des prédicats primitifs supplémentaires indépendants de ces constructions.

## 6. Identité et indexation constitutive

Une fois les occurrences constituées, déterminées et distinguées, se pose la question de leur identité à travers les transformations.

> Que signifie dire qu’il s’agit encore de la même détermination ailleurs ?

L’identité n’est pas définie par l’égalité des lectures, des valeurs, des représentations ou des statuts.

Elle est comprise comme la **persistance démontrée d’une identité déjà constituée lorsqu’elle reste suivie par son indexation constitutive ou par son prolongement canonique sous extension**.

### 6.1 Genèse de l’indexation

L’indexation intervient après la constitution.

Elle n’est pas calculée à partir d’une valeur ou d’un readout.

Elle ne remplace pas non plus le rôle constitutif.

```text
construction
        ↓
occurrences constituées
        ↓
structure d’indexation
        ↓
suivi des identités
```

Le rôle constitutif répond à :

> Qu’est-ce qui détermine cette occurrence ?

L’indexation répond à :

> Comment suivre cette occurrence une fois qu’elle est constituée ?

Il faut donc distinguer :

```text
détermination constitutive
≠
indexation d’identité
```

Lorsqu’une construction s’étend, les anciennes identités sont conservées et une nouvelle identité peut apparaître.

```text
identités à l’étape n
        ↓
extension
        ↓
anciennes identités conservées
+
nouvelle identité
```

Les identités apparues à des étapes distinctes restent distinctes lorsqu’elles sont transportées vers une profondeur commune ultérieure.

### 6.2 Trois niveaux de carrier

La théorie distingue trois niveaux qu’il ne faut pas confondre.

Le premier est le **carrier canonique d’indexation des identités**.

Dans la théorie générique, son carrier initial est abstrait. À chaque extension, cette structure conserve les identités déjà indexées et ajoute une nouvelle identité.

Le deuxième est le **carrier constitutif d’occurrences** d’une construction particulière.

Le troisième est le **carrier concret de réalisation**.

```text
carrier canonique d’indexation
        ↕
carrier constitutif d’occurrences
        ↕
carrier concret de réalisation
```

Le carrier canonique fournit le repère commun permettant de suivre les identités.

Le carrier constitutif contient les occurrences effectivement constituées dans la construction considérée.

Le carrier concret contient leur réalisation particulière.

Dans l’instance circulaire, le raccord devient explicite : **le carrier initial des occurrences constituées est celui du périmètre déjà reconstruit**, puis les extensions successives ajoutent les occurrences nouvelles produites par la construction.

Ainsi :

```text
occurrences du périmètre
        ↓
carrier initial de l’instance circulaire
        ↓
extension
        ↓
anciennes occurrences
+
nouvelle occurrence
```

Le carrier canonique d’indexation est alors raccordé exactement à ces occurrences effectivement constituées des histoires générées.

Ces niveaux sont reliés exactement, mais ne sont pas identifiés.

Une même identité peut donc recevoir plusieurs réalisations sans être définie par aucune d’entre elles.

### 6.3 Le résiduel comme identité suivie

L’instance circulaire fournit un cas particulièrement important.

L’identité fraîche introduite par la transition constitutive canonique est exactement l’occurrence résiduelle déterminée précédemment.

```text
occurrence résiduelle unique
=
identité fraîche de la transition
```

Cette identification ne repose donc pas sur une ressemblance entre deux objets indépendamment construits.

Dans cette instance, les deux descriptions se raccordent au même objet constitutif.

Ainsi, lorsque la théorie passe à la persistance, elle ne commence pas avec un identifiant abstrait dont l’origine serait indéterminée.

Elle suit une occurrence dont la constitution, le rôle et l’unicité ont déjà été établis.

---

## 7. Persistance

La persistance concerne deux types de changement : le changement de réalisation et l’extension de la construction.

Avant de les étudier, il faut distinguer deux usages du terme **exactitude** dans la théorie.

Dans la reconstruction circulaire, l’**exactitude constitutive locale** exprime l’accord entre une exigence structurelle et l’occurrence qui la réalise.

Dans la théorie de la persistance, un **transport exact** désigne une correspondance réversible entre deux carriers.

```text
exactitude constitutive locale
≠
transport exact
```

Ces notions coopèrent dans l’architecture générale, mais elles ne sont pas la même structure formelle.

### 7.1 Transport exact

Un **transport exact** est une correspondance bidirectionnelle entre deux carriers telle que chaque élément puisse être récupéré exactement après un aller-retour.

```text
Source  ──forward──▶  Target
Source  ◀─backward──  Target

backward(forward(x)) = x
forward(backward(y)) = y
```

Cette exactitude garantit l’absence de perte ou de fusion des éléments.

Mais elle ne suffit pas à établir la persistance d’une identité constituée.

Une correspondance peut être parfaitement exacte tout en permutant deux identités.

Il faut donc distinguer :

```text
transport exact quelconque
≠
transport d’identité induit
```

### 7.2 Changement de réalisation

À une profondeur constitutive donnée, deux réalisations sont coordonnées à travers le même index canonique.

```text
occurrence dans A
        ↓
index constitutif commun
        ↓
occurrence dans B
```

Le transport d’identité n’est donc pas obtenu en comparant directement les deux objets concrets.

Il revient à l’index constitutif de la source puis réalise **ce même index** dans le carrier cible.

```text
A(i)
        ↓
i
        ↓
B(i)
```

La correspondance est ainsi déterminée par l’identité constitutive commune.

### 7.3 Extension de la construction

Lorsque la profondeur change, l’identité antérieure reçoit une image canonique dans le carrier ultérieur.

```text
identité à la profondeur n
        ↓
extension canonique
        ↓
même identité à une profondeur ultérieure
```

Cette extension est injective.

Les distinctions déjà établies sont donc conservées.

Une identité antérieure ne fusionne pas avec une identité fraîche et deux identités apparues à des profondeurs différentes ne deviennent pas égales dans un carrier ultérieur commun.

### 7.4 Deux axes de persistance

On obtient deux directions :

```text
horizontal :
changement de réalisation
→ même index

vertical :
extension
→ image canonique de l’identité
```

Ces deux directions doivent être compatibles.

### 7.5 Conservation de l’identité et conservation des propriétés

La persistance d’une identité ne transporte pas automatiquement toutes les propriétés associées à cette identité.

```text
identité conservée
≠
toutes les propriétés conservées
```

Le transport constitutif suit l’identité.

La conservation d’un ordre, d’un rôle, d’une provenance, d’une lecture, d’une valeur ou d’un statut demande une preuve supplémentaire.

```text
identité
        ↓
transport constitutif
        ↓
persistance

propriété supplémentaire
        ↓
preuve spécifique
        ↓
conservation de cette propriété
```

Ainsi :

```text
même détermination
≠ même représentation
≠ même valeur
≠ même statut
```

Une occurrence peut changer de réalisation ou de statut sans que l’identité constitutive suivie soit perdue.

---

## 8. Alignement

L’alignement n’est pas le point de départ de la théorie.

Il apparaît à l’issue de la constitution, de l’indexation et de la persistance.

Pour que les transports d’identité constituent un alignement, ils doivent être cohérents.

### 8.1 Composition des changements de réalisation

Un passage composé doit s’accorder avec le passage direct :

```text
A → B → C
=
A → C
```

L’introduction d’une réalisation intermédiaire ne doit pas changer l’identité obtenue à l’arrivée.

### 8.2 Composition des extensions

Deux extensions successives doivent s’accorder avec leur composition :

```text
profondeur n
→ profondeur m
→ profondeur p

=

profondeur n
→ profondeur p
```

L’introduction d’une profondeur intermédiaire ne doit pas changer l’identité transportée.

### 8.3 Naturalité entre extension et réalisation

Les deux axes doivent commuter :

```text
extension
puis changement de réalisation

=

changement de réalisation
puis extension
```

Autrement dit :

```text
réalisation A à la profondeur s
        ───── extension ─────→
réalisation A à la profondeur t
        │                         │
        │ transport               │ transport
        ↓                         ↓
réalisation B à la profondeur s
        ───── extension ─────→
réalisation B à la profondeur t
```

Cette condition est essentielle.

Une bijection exacte arbitraire peut conserver les aller-retour tout en permutant les identités fraîches et en faisant échouer ce carré.

La cohérence n’est donc pas une conséquence automatique de l’exactitude.

Elle exprime la compatibilité des transports avec l’indexation constitutive.

### 8.4 Définition de l’alignement

Dans ce cadre :

> **l’alignement est la cohérence des transports d’identité induits par une indexation constitutive commune, grâce auxquels une identité déjà constituée est suivie à travers les extensions et les réalisations distinctes.**

La chaîne complète devient ainsi :

```text
constitution
        ↓
rôle constitutif relationnel
        ↓
dépendances
        ↓
séparation et reconstruction
        ↓
instance circulaire
        ↓
reconstruction du périmètre
        ↓
délimitation de l’interne
        ↓
continuation
        ↓
résiduel et unicité
        ↓
classification exacte du régime
        ↓
frontière constitutive
        ↓
longueur dérivée
        ↓
identité
        ↓
indexation
        ↓
persistance
        ↓
cohérence
        ↓
alignement
```

L’alignement ne constitue donc pas l’identité.

**Il établit la cohérence des transports par lesquels une identité déjà constituée est suivie à travers les réalisations et les extensions.**
