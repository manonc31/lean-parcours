# 🎓 Parcours Lean — commencer ici

Un parcours d'exercices pour apprendre **Lean 4** en reconstruisant les mathématiques (et un peu
d'informatique) **depuis zéro** : la logique, les entiers de Peano, les listes, l'arithmétique…
jusqu'au petit théorème de Fermat, aux compilateurs prouvés corrects, et à quelques monstres
(Goodstein, réciprocité quadratique, Church-Rosser) et problèmes ouverts (Collatz, Goldbach).

Les exercices **dépendent les uns des autres** : ce que tu prouves dans un exercice, tu le
réutilises dans les suivants. Une carte interactive te montre ce que tu peux faire ensuite.

---

## 1. Démarrer (5 minutes)

Tout est déjà installé sur ce Mac (Lean 4.35 via `elan`, extension Lean 4 de VS Code).

1. Ouvre le **dossier** `Lean Parcours` dans VS Code (*Fichier → Ouvrir le dossier…*).
2. Dans le terminal de VS Code (`` Ctrl+` ``), lance une première vérification
   (compile tout, environ 30 secondes la première fois) :
   ```
   ./parcours verifier
   ```
3. Ouvre le premier exercice : `Exercices/Tutoriel/Bienvenue.lean`.
4. Ouvre l'**infoview** de Lean : `Cmd+Shift+Enter` (ou l'icône ∀ en haut à droite de l'éditeur).
   Place le curseur sur le `sorry` : l'infoview montre ce qu'il reste à prouver.
5. Remplace `sorry` par ta preuve. Le message de la ligne `#verifier` (tout en bas du fichier,
   visible dans l'infoview ou en survolant la ligne) te dit si c'est réussi.

> Sur un autre Mac : `brew install elan-init`, puis ouvre le dossier dans VS Code avec
> l'extension **Lean 4** (VS Code la propose automatiquement). La première ouverture télécharge
> Lean 4.35 tout seul.

---

## 2. La commande `./parcours`

| Commande | Effet |
|---|---|
| `./parcours` | ce que tu peux faire maintenant |
| `./parcours verifier` | recompile, vérifie tout, met à jour la carte et la progression |
| `./parcours carte` | ouvre la **carte interactive** (`progression.html`) dans le navigateur |
| `./parcours arbre [branche]` | l'arbre complet (ou une branche : `./parcours arbre logique`) |
| `./parcours branches` | les branches et ta progression |
| `./parcours info <exo>` | l'énoncé et les dépendances d'un exercice |
| `./parcours indice <exo>` | révèle **un** indice de plus (relance pour le suivant) |
| `./parcours solution <exo>` | affiche la solution (demande confirmation) |
| `./parcours ouvrir <exo>` | ouvre l'exercice dans VS Code |
| `./parcours reset <exo>` | remet un exercice à zéro (ton travail est sauvegardé) |

`<exo>` peut être approximatif : `addcomm`, `Naturels.AddComm`, `commutativ`…

Dans VS Code, `Cmd+Shift+B` lance aussi `./parcours verifier` (tâche par défaut), et
*Terminal → Exécuter la tâche…* propose les autres.

---

## 3. Les règles du jeu

### États d'un exercice
- 🎯 **disponible** : tous les exercices dont il dépend sont réussis.
- 🔒 **verrouillé** : il faut d'abord réussir ses dépendances. (Tu peux quand même l'ouvrir
  et le faire : les résultats non prouvés que tu utilises sont juste signalés.)
- ✅ **réussi** : plus aucun `sorry`, l'énoncé n'a pas été modifié.
- ⭐ **pur** : réussi **sans emprunter** de théorème à la bibliothèque de Lean (voir ci-dessous).
- 📖 **cours** : un fichier sans exercice, qui pose des définitions.
- 🌉 **pont** · 💀 **boss** (très dur, parfois sans solution de référence) · ♾️ **problème ouvert** ·
  🏆 **théorème célèbre** (de la liste des « 100 théorèmes » de Freek Wiedijk).

### Recoder d'abord, utiliser la bibliothèque ensuite
La bibliothèque de Lean contient déjà `Nat.add_comm`, `List.reverse_reverse`, la tactique `omega`…
Mais l'idée du parcours est de **tout reconstruire toi-même**. Au début, tu travailles sur des
objets refaits à la main (ton `ℕ` de Peano, tes `Liste`…) : la bibliothèque ne peut pas t'aider.

Puis viennent les **Ponts** 🌉 : par exemple « mon `ℕ` et le `Nat` de Lean sont le même objet ».
Un pont **débloque** une partie de la bibliothèque pour tous les exercices qui en dépendent :

| Pont | Débloque |
|---|---|
| Logique · *Le grand examen de logique* | les lemmes de logique (`and_comm`, `not_not`…) |
| Naturels · *Le pont vers les entiers de Lean* | `Nat.*`, `Int.*` et la tactique `omega` |
| Naturels · *L'identité remarquable* | la tactique `grind` (calculs algébriques automatiques) |
| Listes · *Le pont vers les listes de Lean* | `List.*`, `simp` sur les listes |
| Arithmétique · *Le pont arithmétique* | `∣`, `Nat.gcd`, nombres premiers de la bibliothèque |

Si tu utilises un lemme pas encore débloqué, l'exercice est quand même ✅ réussi, mais pas ⭐ :
le message de `#verifier` te dit lesquels tu as « empruntés ». Tu pourras revenir chercher l'étoile.

Quelques exercices **interdisent** certaines choses (par exemple la logique classique dans
« Diaconescu ») : le vérificateur refuse alors la preuve.

### Les dépendances sont de vrais `import`
Quand un exercice importe `Exercices.Naturels.AddComm`, il utilise **ton** fichier, donc **ta**
preuve de `add_comm`. Conséquence : si un fichier a une **erreur** (pas un `sorry`, une vraie
erreur), les exercices qui l'importent ne peuvent pas être compilés. Remets temporairement
`sorry` à la place d'une preuve cassée pour avancer ailleurs.

### Ne modifie pas les énoncés
Tu peux ajouter tes propres lemmes intermédiaires (`theorem mon_lemme …`) où tu veux, mais ne
modifie pas l'énoncé des théorèmes à prouver (le vérificateur le détecte), ni les définitions
données.

---

## 4. Les branches

| Branche | Contenu |
|---|---|
| 🎓 Tutoriel | l'infoview, `rfl`, `rw`, `exact`, `apply`, ta première étoile |
| 🏋️ Gymnase | des petits exercices, une tactique à la fois |
| 🧠 Logique | →, ∧, ∨, ¬, ↔, ∀, ∃, logique classique, Cantor, Russell, Diaconescu |
| 🔢 Entiers naturels | ℕ de Peano : +, ×, ^, ≤, récurrence forte, bon ordre, pont vers `Nat` |
| 🔀 Fonctions & ensembles | injections, surjections, axiome du choix, Knaster–Tarski, Cantor–Bernstein |
| 🪜 Récurrence & sommes | Gauss, Nicomaque, Bernoulli, Fibonacci, Cassini |
| 🖼️ Classiques à visualiser | des faits célèbres à se représenter puis à formaliser : nombres figurés, pizza, Fibonacci, divisibilité, Cauchy-Schwarz, Brahmagupta, log₂ 3, taxi de Ramanujan |
| 📋 Listes | listes refaites à la main, miroir, plis, pont vers `List` |
| 📊 Tris | insertion, sélection, fusion, rapide (programmés et prouvés), borne n log n |
| ⚙️ Algorithmes | exponentiation rapide, dichotomie, ABR, files, RLE, Horner |
| 🕹️ Programmes ludiques | FizzBuzz, César, multiplication russe, huit reines, mélange du magicien, Luhn, chiffres romains, Boyer-Moore, sac à dos, jeu de la vie… |
| 🔐 Arithmétique | PGCD, Bézout, Gauss, Euclide, √2, décomposition en premiers, Fermat, restes chinois |
| 🧮 Combinatoire | binôme de Newton, tiroirs, crosse de hockey, anagrammes, dérangements, Catalan, hôtel de Hilbert, Ramsey |
| 🕸️ Graphes | degrés, chemins, coloriages, ponts de Königsberg, maison du père Noël, graphe de Petersen |
| 🏗️ Constructions | ℤ et ℚ par quotients, réels de Dedekind |
| 📈 Analyse | suites et limites sur ℚ, gendarmes, suites de Cauchy |
| 💎 Algèbre | groupes depuis les axiomes, sous-groupes, morphismes, anneaux, symétries du triangle, Rubik's cube |
| 🔲 Matrices | matrices 2×2, déterminant, inverse, Fibonacci par les matrices |
| 🔌 Binaire & circuits | additionneurs prouvés corrects, conversion binaire, code de Gray, NAND universelle |
| 💻 Informatique théorique | compilateur prouvé, IMP, logique de Hoare, automates, arrêt, λ-calcul, RSA, code de Hamming, castor affairé |
| ♻️ Terminaison | Ackermann, McCarthy 91, Syracuse, Goodstein |
| 🎮 Théorie des jeux | Nim, Zermelo, dilemme du prisonnier, donnant-donnant, jeu de 15 |
| 🎲 Probabilités | dés, Monty Hall, anniversaires, Markov, loi binomiale, Galilée, problème des partis, Simpson, faux positifs |
| 🧩 Énigmes | chevaliers et menteurs, la dame ou le tigre, bidons, missionnaires, pont et lampe, cavalier, sudoku, taquin, vendredi 13, McNuggets, Hanoï, Josèphe |
| 🏅 Olympiades | problèmes de compétition, descente infinie, Pell-Fermat, dont IMO 1959, 1964, 1977, 1988 |
| ♾️ Problèmes ouverts | Collatz, Goldbach, jumeaux, nombres parfaits impairs… |

---

## 5. Aide

- **`AIDE_TACTIQUES.md`** : toutes les tactiques utiles, en français, avec exemples.
- Bloqué·e ? `./parcours indice <exo>` (les indices sont progressifs), ou la carte interactive.
- Pour chercher un lemme : tape `exact?` dans une preuve, Lean propose des candidats.
  (Attention, ils viennent souvent de la bibliothèque : pas d'étoile avant le pont !)
- Ressources générales :
  - [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) (le livre de référence)
  - [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
  - [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
  - [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)
  - [Zulip de la communauté Lean](https://leanprover.zulipchat.com/) (on y répond aux questions de débutants)

### Organisation des dossiers
- `Exercices/` : **ton** travail (c'est le seul dossier que tu modifies).
- `Solutions/` : les solutions de référence (masquées dans VS Code pour éviter de te spoiler).
- `ParcoursOutils/`, `ParcoursCli.lean` : le vérificateur et la commande `./parcours` (écrits en Lean !).
- `Outils/` : le générateur du parcours et le modèle de la carte.
- `.parcours/` : données (graphe des exercices, ta progression, indices révélés).

### Conseil
Mets ton travail sous `git` pour garder un historique de ta progression :
```
git init && git add -A && git commit -m "Début du parcours"
```
