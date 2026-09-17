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

### Positionnement

Cette théorie se situe à proximité de travaux sur la clôture organisationnelle, les touts relationnels, l’individuation, les frontières structurelles et l’identité. Sa contribution propre ne réside pas dans l’une de ces notions prise isolément, mais dans l’ordre constructif qui les relie : reconstruction d’un domaine constitutif, détermination du nouveau relativement à ce domaine, formation d’une frontière de régime, genèse d’une identité fraîche puis persistance cohérente de cette identité. Le positionnement comparatif détaillé est présenté dans [POSITIONNEMENT_SCIENTIFIQUE.md](POSITIONNEMENT_SCIENTIFIQUE.md).

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

**Le périmètre reconstruit constitue ainsi un tout constitutif : une unité structurelle dont les relations constitutives suffisent à déterminer canoniquement leur propre domaine d’intériorité. Sa complétude consiste dans cette détermination positive de l’interne.**

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

Dans ce qui suit, les termes **identité**, **détermination constitutive**, **persistance** et **alignement** donnent une lecture théorique de structures et d’équations formelles explicites. Le développement Lean vérifie directement les occurrences, indexations, transports exacts, extensions, compositions, séparations et lois de naturalité qui contraignent cette lecture. Ces termes ne sont pas introduits comme des prédicats primitifs supplémentaires indépendants de ces constructions.

## 6. Identité et indexation constitutive

Une fois les occurrences constituées, déterminées et distinguées, se pose la question de leur identité à travers les transformations.

> Que signifie dire qu’il s’agit encore de la même détermination ailleurs ou plus tard dans la construction ?

L’identité n’est pas définie par l’égalité des lectures, des valeurs, des représentations ou des statuts.

Elle est comprise comme la **persistance démontrée d’une détermination déjà constituée lorsqu’elle reste suivie par son indexation constitutive ou par son prolongement canonique sous extension**.

L’ordre est donc essentiel :

```text
constitution
        ↓
détermination d’une occurrence
        ↓
genèse éventuelle d’une nouvelle occurrence
        ↓
indexation de cette identité
        ↓
persistance
```

L’indexation ne produit pas l’identité. Elle fournit le moyen de suivre une identité dont la genèse a déjà été établie.

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

La distinction ancien / nouveau devient ainsi une structure d’identité, et non seulement une différence de position dans une histoire.

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

### 6.3 Le résiduel comme genèse de l’identité fraîche

L’instance circulaire fournit le raccord décisif entre la théorie de la frontière et la théorie de l’identité.

L’identité fraîche introduite par la transition constitutive canonique est exactement l’occurrence résiduelle déterminée précédemment.

```text
occurrence résiduelle unique
=
identité fraîche de la transition
```

Cette identification ne repose pas sur une ressemblance entre deux objets indépendamment construits.

Le résiduel est d’abord déterminé relativement au tout constitutif reconstruit. Cette même occurrence devient ensuite l’identité fraîche de la structure d’extension.

```text
tout constitutif
        ↓
continuation
        ↓
résiduel unique
        ↓
identité fraîche
```

Ainsi, lorsque la théorie passe à la persistance, elle ne commence pas avec un identifiant abstrait dont l’origine serait indéterminée.

Elle suit une occurrence dont la constitution, le rôle résiduel, l’unicité et la relation à la frontière ont déjà été établis.

### 6.4 Provenance structurelle des identités finies

L’itération finie ne se contente pas de conserver des éléments dans des carriers successifs. Elle conserve une information structurelle sur leur provenance.

Le carrier canonique à profondeur `n` a la forme récursive :

```text
IteratedCarrier Initial 0
=
Initial

IteratedCarrier Initial (n + 1)
=
IteratedCarrier Initial n + Unit
```

Une identité est donc soit une identité initiale, soit une identité fraîche apparue à une étape déterminée.

Le développement construit un code structurel :

```text
identityCode :
identité à une profondeur finie
→ identité initiale + profondeur de genèse
```

Ce code possède trois propriétés importantes.

Premièrement, il est injectif à toute profondeur fixée : il ne fusionne pas deux identités distinctes du même carrier.

Deuxièmement, il est invariant sous extension : prolonger une identité dans un carrier ultérieur ne change pas son code.

Troisièmement, deux identités fraîches apparues à des profondeurs distinctes restent distinctes lorsqu’elles sont plongées dans un même carrier ultérieur.

```text
identité constituée à l’étape m
        ↓ extension
même provenance structurelle

identité constituée à l’étape n
        ↓ extension
même provenance structurelle

m ≠ n
        ↓
identités toujours distinctes
```

La profondeur joue ici le rôle d’un index de genèse dans la construction finie. Elle n’est pas une horloge extérieure ajoutée aux occurrences.

Cette structure donne à la persistance une propriété plus forte que la simple survie d’un élément : **l’identité persiste avec la trace structurelle de son origine constitutive dans la chaîne d’extensions.**

### 6.5 L’identité précède l’alignement

L’alignement ne doit donc pas être compris comme un mécanisme qui fabriquerait après coup l’identité commune de plusieurs réalisations.

Dans l’ordre de dépendance actuel :

```text
constitution
        ↓
identité déterminée
        ↓
indexation
        ↓
réalisations exactes
        ↓
transports
        ↓
alignement
```

Ce qui sera aligné doit d’abord être constitué et indexé.

Cette priorité interdit de remplacer l’identité par un matching entre sorties, par une égalité de valeurs ou par une bijection choisie après observation des réalisations.

---

## 7. Persistance

La persistance étudie comment une identité déjà constituée reste suivie sous deux types de changement : le changement de réalisation et l’extension de la construction.

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

Cette exactitude garantit l’absence de perte ou de fusion des éléments relativement au transport considéré.

Mais elle ne suffit pas à établir la persistance d’une identité constituée.

Une correspondance peut être parfaitement exacte tout en permutant deux identités.

Il faut donc distinguer :

```text
transport exact quelconque
≠
transport d’identité induit
```

### 7.2 Changement de réalisation : axe horizontal

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

Le transport entre réalisations est ainsi dérivé des deux raccords au même index.

Il n’est pas stocké comme une donnée de matching pair à pair indépendante.

### 7.3 Extension de la construction : axe vertical

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

### 7.4 Indépendance vis-à-vis du témoin d’extension

Une extension finie `DepthExtension source target` est proof-relevant : plusieurs témoins peuvent décrire un passage entre les mêmes profondeurs.

Le développement ne prétend pas que ces témoins de preuve sont eux-mêmes égaux.

Il établit autre chose, plus directement pertinente pour la persistance : **l’image d’une identité dépend des profondeurs source et cible, pas du témoin particulier choisi entre elles.**

```text
d₁ : DepthExtension s t
d₂ : DepthExtension s t
        ↓
embedFrom d₁(x)
=
embedFrom d₂(x)
```

La même indépendance est démontrée pour les extensions concrètes induites entre réalisations.

La persistance est donc indépendante du chemin proof-relevant choisi pour certifier une même extension finie, sans effacer pour autant la structure de ces témoins.

### 7.5 Persistance de l’occurrence résiduelle réelle

L’instance circulaire raccorde cette théorie générique aux histoires effectivement produites.

À la profondeur un, l’identité fraîche est exactement l’occurrence résiduelle opérationnelle.

Cette identité est ensuite prolongée à toute profondeur finie ultérieure fournie.

```text
résiduel à la première frontière
        =
identité fraîche à la profondeur 1
        ↓
extension finie
        ↓
même identité à une profondeur ultérieure
```

Le changement de réalisation préserve également cette identité, et la persistance de cette occurrence résiduelle commute avec le changement de réalisation.

La chaîne obtenue est donc :

```text
genèse du résiduel
        ↓
identité fraîche
        ↓
persistance verticale
        +
transport horizontal
        ↓
même identité suivie dans des réalisations distinctes
```

La persistance ne porte donc pas sur une identité générique sans origine. Elle porte, dans l’instance circulaire, sur une identité dont la genèse au niveau de la frontière a été formellement raccordée à l’occurrence résiduelle.

### 7.6 Conservation de l’identité et conservation des propriétés

La persistance d’une identité ne transporte pas automatiquement toutes les propriétés associées à cette identité.

```text
identité conservée
≠
toutes les propriétés conservées
```

Le transport constitutif suit l’identité.

La conservation d’un ordre, d’un rôle, d’une provenance supplémentaire, d’une lecture, d’une valeur, d’un statut ou d’une propriété sémantique demande une preuve spécifique.

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

### 7.7 De la persistance à l’alignement

La persistance fournit désormais deux familles de transformations :

```text
horizontal :
changement de réalisation
→ même index constitutif

vertical :
extension
→ prolongement canonique de l’identité
```

L’existence séparée de ces deux familles ne suffit pas encore à constituer un alignement.

L’alignement commence lorsque l’on demande que leurs compositions soient cohérentes et que les différents chemins structurellement légitimes conduisent à la même identité.

---

## 8. Alignement constitutif

L’alignement n’est pas le point de départ de la théorie.

Il est la couche de cohérence obtenue après la constitution, la genèse des identités, leur indexation et leur persistance.

La question n’est donc pas :

> Deux réalisations se ressemblent-elles ?

mais :

> **Les transformations entre réalisations et entre profondeurs suivent-elles de manière cohérente les mêmes identités déjà constituées ?**

### 8.1 Alignement constitutif et adéquation normative

Deux relations doivent rester distinctes.

L’**alignement constitutif** étudié ici concerne la cohérence des transports d’identité à travers les réalisations et les extensions.

L’**adéquation d’un régime à une spécification indépendante** concerne la relation entre admission opérationnelle et satisfaction d’une norme.

```text
alignement constitutif
=
cohérence des identités transportées

adéquation normative
=
relation entre régime et spécification
```

Aucune de ces relations ne doit être utilisée pour définir l’autre.

Dans cette présentation, le terme **alignement** désigne désormais l’alignement constitutif sauf indication contraire.

### 8.2 Ordre de dépendance de l’alignement

L’alignement possède lui aussi un ordre de dépendance.

```text
identités déjà constituées
        ↓
indexation constitutive commune
        ↓
réalisations exactes de cet index
        ↓
transports horizontaux induits
        +
extensions verticales induites
        ↓
composition
        ↓
naturalité
        ↓
alignement constitutif
```

Cet ordre interdit deux raccourcis.

Premièrement, une correspondance exacte entre carriers n’est pas encore un alignement.

Deuxièmement, une similarité de lectures ou de valeurs ne peut pas remplacer l’indexation constitutive commune.

L’alignement est donc **dérivé de la constitution** plutôt qu’ajouté extérieurement comme une relation de comparaison.

### 8.3 L’index commun comme médiateur constitutif

Le principe architectural central est qu’une réalisation `A` et une réalisation `B` ne sont pas d’abord mises en correspondance directement.

Elles sont chacune raccordées exactement au même carrier constitutif canonique.

```text
                  index constitutif commun
                    /              \
                   /                \
                  ↓                  ↓
           réalisation A       réalisation B
```

Le transport `A → B` est ensuite dérivé par retour vers cet index puis réalisation dans `B`.

À un pas, l’index expose la décomposition exacte :

```text
Initial + Unit
        ≃
Extended
```

À profondeur finie, l’index est `IteratedCarrier` et conserve les identités initiales ainsi que la profondeur de genèse de chaque identité fraîche.

Cette architecture donne à l’alignement un caractère relationnel de second ordre : **deux réalisations sont coordonnées parce qu’elles réalisent exactement une même détermination constitutive, et non parce qu’un matching indépendant a été choisi entre elles.**

Dans l’état actuel de la théorie, cet index commun est fourni ou extrait d’une construction commune. La théorie ne prétend pas encore reconstruire automatiquement un tel médiateur entre deux systèmes initialement présentés comme indépendants.

### 8.4 Décomposition ancien / nouveau et unicité relative du transport

À un pas, toute identité du carrier étendu est constructivement classée comme :

```text
ancienne identité
ou
identité fraîche
```

Cette décomposition complète permet un résultat d’unicité relative important.

Supposons qu’un transport candidat entre deux réalisations du carrier étendu :

1. envoie chaque ancienne identité vers l’ancienne identité correspondant au même index constitutif ;
2. envoie l’identité fraîche vers l’identité fraîche.

Alors son action est déterminée ponctuellement sur tout le carrier étendu : elle coïncide avec le transport induit par l’index commun.

```text
accord sur toutes les anciennes identités
+
accord sur l’identité fraîche
        ↓
transport déterminé sur tout le carrier étendu
```

Ce résultat ne dit pas que toute bijection exacte possible entre deux carriers est unique.

Il dit que **le transport constitutivement compatible est déterminé dès que son action est fixée sur la décomposition constitutive complète ancien / nouveau.**

Cette distinction est essentielle pour éviter de confondre unicité relative de l’alignement et unicité absolue de toute correspondance exacte.

### 8.5 Composition horizontale et composition verticale

La cohérence exige d’abord que les chemins composés ne dépendent pas d’un intermédiaire arbitraire.

Pour les changements de réalisation :

```text
A → B → C
=
A → C
```

Le passage par une réalisation intermédiaire ne change pas l’identité finale obtenue.

Pour les extensions :

```text
profondeur n
→ profondeur m
→ profondeur p

=

profondeur n
→ profondeur p
```

Le passage par une profondeur intermédiaire ne change pas le prolongement final de l’identité.

À cela s’ajoute l’indépendance vis-à-vis du témoin d’extension étudiée précédemment.

La cohérence n’est donc pas seulement locale à un carré. Elle possède déjà une structure de composition le long de chacun des deux axes.

### 8.6 Naturalité entre extension et changement de réalisation

Les deux axes doivent ensuite commuter.

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

La loi est :

```text
transport après extension
=
extension après transport
```

Elle signifie qu’une identité ne dépend pas de l’ordre dans lequel on effectue les deux changements structurellement légitimes.

```text
étendre puis changer de réalisation
=
changer de réalisation puis étendre
```

Cette naturalité fournit la cohérence bidimensionnelle de la persistance.

Elle ne dit pas que les réalisations sont identiques. Elle dit que les chemins par lesquels une même identité constituée est suivie dans ces réalisations sont compatibles.

### 8.7 L’exactitude seule ne suffit pas : séparateur dynamique

L’insuffisance de l’exactitude seule n’est pas seulement déclarative.

Le développement contient un séparateur constructif.

À profondeur finie, on peut construire une permutation exacte et bijective qui échange deux identités fraîches tout en conservant des aller-retour parfaits.

```text
transport exact
+
bijectif
+
aller-retour exact
```

mais :

```text
carré d’extension / transport
ne commute pas
```

La même séparation est instanciée entre deux réalisations concrètes effectivement utilisées par le projet.

On obtient donc la non-implication :

```text
exactitude du transport
⇏
naturalité constitutive
```

et, par conséquent :

```text
bijection exacte arbitraire
≠
alignement constitutif
```

Ce séparateur joue pour l’alignement le même rôle méthodologique que les carriers affaiblis jouent plus tôt pour l’ordre et l’adjacence : il localise une dépendance qui ne peut pas être absorbée silencieusement dans une notion plus faible.

### 8.8 Cohérence médiée

La naturalité possède une lecture plus générale.

Deux chemins concrets n’ont pas besoin d’être identifiés directement pour montrer qu’ils sont cohérents. Il suffit d’abord qu’ils réalisent la même transition dans un médiateur commun.

Schématiquement :

```text
chemin concret A
        ↘
         transition commune dans M
        ↗
chemin concret B
```

Lorsque les deux chemins réalisent la même transition dans le médiateur, leurs observations terminales dans ce médiateur coïncident.

Cette **commutation observée** ne demande aucune hypothèse de fidélité globale.

```text
même transition médiée
        ↓
commutation observée
```

Pour relever cette égalité observée en une égalité littérale des sorties concrètes, une propriété de réflexion au point terminal suffit.

```text
commutation observée
+
réflexion terminale locale
        ↓
commutation littérale
```

L’injectivité globale de l’observation terminale est une condition suffisante plus forte qui fournit cette réflexion.

Dans l’alignement constitutif fini, le médiateur est précisément `IteratedCarrier`. Les raccords exacts rendent l’observation terminale suffisamment fidèle pour récupérer la naturalité littérale déjà établie.

Cette factorisation est conceptuellement importante : **la cohérence provient d’abord du fait que les deux chemins réalisent la même transition constitutive médiée. L’égalité concrète est ensuite récupérée lorsque l’observation terminale permet de réfléchir cette égalité.**

Les carrés médiés adjacents peuvent en outre être composés au niveau observé sans exiger de fidélité à leur frontière intermédiaire. Une réflexion au terminal extérieur suffit pour relever le rectangle composé en une commutation littérale.

La couche d’alignement dispose ainsi d’une propriété de collage qui ne demande pas de rendre chaque intermédiaire globalement fidèle.

### 8.9 Alignement de la nouveauté constituée

Le raccord entre résiduel et identité fraîche donne maintenant un sens plus précis à l’alignement du nouveau.

Dans l’instance circulaire :

```text
résiduel unique
=
identité fraîche
```

et le transport entre réalisations envoie l’identité fraîche de `A` sur l’identité fraîche de `B`.

Donc deux réalisations exactes de la même continuation ne déterminent pas indépendamment deux nouveautés qu’il faudrait ensuite rapprocher par similarité.

Elles réalisent **la même occurrence nouvelle déjà déterminée dans le carrier constitutif commun**.

```text
frontière constitutive
        ↓
résiduel unique
        ↓
identité fraîche commune
       / \
      /   \
     ↓     ↓
    A       B
```

L’alignement du nouveau est ainsi une **co-réalisation d’une même genèse constitutive**, et non un matching postérieur entre deux sorties nouvelles.

Cette propriété est ensuite stable sous extension finie : l’identité née à la première frontière reste suivie aux profondeurs ultérieures et cette persistance commute avec le changement de réalisation.

### 8.10 Définition théorique de l’alignement constitutif

Dans l’état actuel de la théorie :

> **un alignement constitutif est la cohérence d’une famille de transports d’identité induits par une indexation constitutive commune, sous changement de réalisation et extension, de telle sorte que les identités déjà constituées et les identités nouvelles déterminées par la construction restent suivies sans confusion et que les chemins de transport pertinents se composent et commutent.**

Cette définition théorique condense plusieurs structures formelles distinctes :

```text
index commun
+
raccords exacts
+
décomposition ancien / nouveau
+
prolongements injectifs
+
composition horizontale
+
composition verticale
+
naturalité
+
cohérence médiée
```

Elle ne constitue pas un prédicat Lean supplémentaire qui remplacerait ces structures.

Elle en donne la lecture architecturale commune.

L’alignement ne constitue donc pas l’identité.

**Il établit la cohérence des transformations par lesquelles une identité dont la genèse est déjà déterminée reste la même à travers des réalisations et des extensions distinctes.**

### 8.11 Ce que l’alignement actuel n’établit pas encore

La théorie actuelle fournit un noyau précis d’alignement constitutif, mais sa frontière doit rester explicite.

Elle ne démontre pas encore qu’un index constitutif commun peut être reconstruit entre deux systèmes arbitraires initialement donnés sans médiateur commun.

Elle ne démontre pas que l’interface actuelle de l’alignement soit minimale parmi toutes les formalisations possibles.

Elle ne transporte pas automatiquement les rôles, les lectures, les valeurs, les statuts, les normes ou les propriétés sémantiques attachées aux identités.

Elle est actuellement uniforme sur toute profondeur **finie** fournie. Elle ne construit pas un carrier concret à l’étape `ω`.

Enfin, elle ne constitue pas par elle-même une théorie de l’alignement comportemental ou normatif de systèmes d’intelligence artificielle entraînés.

Le problème théorique qui reste ouvert à la frontière de cette couche peut être formulé ainsi :

> **Sous quelles conditions relationnelles peut-on reconstruire un index constitutif commun entre des constructions initialement présentées comme distinctes, au lieu de supposer ou d’extraire cet index d’une construction déjà commune ?**

Cette question prolonge directement la méthode générale du projet : affaiblir, séparer et reconstruire, mais appliquée cette fois à l’alignabilité elle-même.

### 8.12 Chaîne théorique complète

La chaîne complète peut désormais être formulée plus précisément :

```text
relations constitutives
        ↓
individuation
        ↓
rôles constitutifs relationnels
        ↓
analyse des dépendances
        ↓
séparation et reconstruction
        ↓
instance circulaire
        ↓
reconstruction du tout constitutif
        ↓
continuation
        ↓
résiduel unique
        ↓
frontière constitutive du régime
        ↓
identité fraîche
        ↓
indexation et provenance structurelle
        ↓
persistance finie
        ↓
transports induits entre réalisations
        ↓
extensions injectives
        ↓
composition des deux axes
        ↓
naturalité et cohérence médiée
        ↓
alignement constitutif
```

Le mouvement théorique est donc continu.

Le tout constitutif permet de déterminer le nouveau.

Le nouveau déterminé devient une identité.

L’identité reçoit une provenance structurelle et persiste sous extension.

Plusieurs réalisations de cette même détermination sont coordonnées par un index commun.

Enfin, l’alignement exprime la cohérence des chemins par lesquels cette identité constituée traverse ces réalisations et ces extensions.
