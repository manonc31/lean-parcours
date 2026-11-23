import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

AD = "Solutions.Arithmetique.Definitions"
RD = "Solutions.Recurrence.Definitions"
CB = "Solutions.Combinatoire.BinomBase"
CD = "Solutions.Combinatoire.Definitions"
PD = "Solutions.Probabilites.Definitions"
GD = "Solutions.Graphes.Definitions"

def co(ident, titre, diff, imports, texte, code, indices, requiert, ressources=()):
    exo("Combinatoire", ident, titre, diff, imports, texte, code, indices, "Parcours.Combi", requiert=requiert, ressources=ressources)
def pb(ident, titre, diff, imports, texte, code, indices, requiert, ressources=()):
    exo("Probabilites", ident, titre, diff, imports, texte, code, indices, "Parcours.Proba", requiert=requiert, ressources=ressources)
def gr(ident, titre, diff, imports, texte, code, indices, requiert, ressources=()):
    exo("Graphes", ident, titre, diff, imports, texte, code, indices, "Parcours.Graphes", requiert=requiert, ressources=ressources)
def cl(ident, titre, diff, imports, image, enonce, code, indices, requiert, ressources=()):
    texte = "## Se le représenter\n" + image.strip() + "\n\n## À prouver\n" + enonce.strip()
    exo("Classiques", ident, titre, diff, imports, texte, code, indices, "Parcours.Classiques", requiert=requiert, ressources=ressources)

co("CrosseHockey", "La crosse de hockey", 2, [CB],
"""Dans le triangle de Pascal, additionne les nombres d'une diagonale, en partant du bord :
`1 + 3 + 6 + 10 = 20`. Le résultat est juste en dessous, décalé d'un cran : la figure dessine une
**crosse de hockey**.

## À prouver
`crosse_hockey : somme (fun i => binom (i + k) k) (m + 1) = binom (m + k + 1) (k + 1)`""",
"""open Parcours.Recurrence

theorem crosse_hockey (k m : Nat) :
    somme (fun i => binom (i + k) k) (m + 1) = binom (m + k + 1) (k + 1) := by -- @exo
  induction m with
  | zero =>
    simp only [somme_succ, Nat.zero_add]
    rw [binom_self, binom_self]
    rfl
  | succ m ih =>
    rw [somme_succ, ih, show m + 1 + k + 1 = (m + k + 1) + 1 by omega, binom_succ_succ (m + k + 1) k,
      show m + 1 + k = m + k + 1 by omega]
    omega""",
["Récurrence sur `m`. Le cas de base : `binom k k = 1` (`binom_self`).", "Pas de récurrence : la formule de Pascal `binom_succ_succ` sur `binom (m + k + 2) (k + 1)`."], "Combinatoire.SommeLigne",
ressources=["[Identité de la crosse de hockey (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Hockey-stick_identity)"])

co("Symetrie", "Choisir, c'est laisser", 2, ["Solutions.Combinatoire.BinomFact", AD],
"""Choisir les `k` personnes qui partent en voyage, c'est la même chose que choisir les `n − k` qui
restent : `binom n k = binom n (n − k)`. Le triangle de Pascal est symétrique.

## À prouver
`symetrie : k ≤ n → binom n k = binom n (n - k)`""",
"""open Parcours.Recurrence

theorem symetrie (n k : Nat) (h : k ≤ n) : binom n k = binom n (n - k) := by -- @exo
  have h1 := binom_mul_fact h
  have h2 := binom_mul_fact (Nat.sub_le n k)
  rw [Nat.sub_sub_self h] at h2
  have hp : 0 < fact k * fact (n - k) := Nat.mul_pos (Parcours.Arith.fact_pos k) (Parcours.Arith.fact_pos (n - k))
  apply Nat.eq_of_mul_eq_mul_right hp
  grind""",
["Utilise la formule `binom_mul_fact` pour `k` et pour `n − k`.", "Les deux produits valent `n!` ; on simplifie par `k! (n − k)! > 0` (`Nat.eq_of_mul_eq_mul_right`)."], "Combinatoire.BinomFact")

co("Menus", "Le principe multiplicatif", 1, [CD],
"""Au restaurant : 3 entrées, 4 plats, 2 desserts. Combien de menus ? `3 × 4 × 2 = 24`. Pour chaque
entrée, on a 4 plats possibles, et pour chaque couple (entrée, plat), 2 desserts : c'est un
**arbre** dont on compte les feuilles.

## À prouver
1. `longueur_produit` : le nombre de couples `(a, b)` est le produit des nombres de choix.
2. `menus` : 24 menus.""",
"""theorem longueur_produit {α β : Type} (l₁ : List α) (l₂ : List β) :
    (l₁.flatMap fun a => l₂.map fun b => (a, b)).length = l₁.length * l₂.length := by -- @exo
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, ih, List.length_cons,
      Nat.succ_mul]
    omega

def entrees : List String := ["salade", "soupe", "terrine"]
def plats : List String := ["poisson", "poulet", "lasagnes", "curry"]
def desserts : List String := ["glace", "tarte"]

theorem menus : (entrees.flatMap fun e => (plats.flatMap fun p => desserts.map fun d => (p, d)).map
    fun pd => (e, pd)).length = 24 := by -- @exo
  simp [entrees, plats, desserts]""",
["Récurrence sur `l₁` ; `List.flatMap_cons`, `List.length_append`, `List.length_map`.", "Pour les menus, `simp` calcule les longueurs."], "Combinatoire.Tiroirs")

co("Anagrammes", "Les anagrammes", 3, [CD],
"""Combien de façons de ranger `n` objets distincts ? `n! = n × (n − 1) × ⋯ × 1`. Le programme
`perms` construit toutes les permutations : pour ranger `x :: l`, on range `l` puis on **insère**
`x` à chacune des `|l| + 1` places possibles.

Avec des lettres répétées, il y a moins d'anagrammes : « ANNA » n'en a que `4! / (2! × 2!) = 6`.

## À prouver
1. `longueur_inserer`, `mem_inserer`, `mem_perms` : les longueurs.
2. `longueur_perms : (perms l).length = fact l.length`
3. `anna : (perms [0, 1, 1, 0]).eraseDups.length = 6` et `kayak` : 30 anagrammes.""",
"""open Parcours.Recurrence

def inserer (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: l => (x :: y :: l) :: (inserer x l).map (y :: ·)

def perms : List Nat → List (List Nat)
  | [] => [[]]
  | x :: l => (perms l).flatMap (inserer x)

theorem longueur_inserer (x : Nat) (l : List Nat) : (inserer x l).length = l.length + 1 := by -- @exo
  induction l with
  | nil => rfl
  | cons y l ih => simp [inserer, ih]

theorem mem_inserer (x : Nat) (l p : List Nat) (h : p ∈ inserer x l) : p.length = l.length + 1 := by -- @exo
  induction l generalizing p with
  | nil =>
    simp [inserer] at h
    simp [h]
  | cons y l ih =>
    simp only [inserer, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨q, hq, rfl⟩
    · simp
    · simp [ih q hq]

theorem mem_perms (l p : List Nat) (h : p ∈ perms l) : p.length = l.length := by -- @exo
  induction l generalizing p with
  | nil =>
    simp [perms] at h
    simp [h]
  | cons x l ih =>
    simp only [perms, List.mem_flatMap] at h
    obtain ⟨q, hq, hp⟩ := h
    rw [mem_inserer x q p hp, ih q hq]
    rfl

theorem longueur_perms (l : List Nat) : (perms l).length = fact l.length := by -- @exo
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [perms, List.length_flatMap, List.length_cons, fact_succ]
    rw [List.map_congr_left (g := fun _ => l.length + 1)
      (fun q hq => by rw [longueur_inserer, mem_perms l q hq])]
    rw [List.map_const', List.sum_replicate_nat, ih, Nat.mul_comm]

theorem anna : (perms [0, 1, 1, 0]).eraseDups.length = 6 := by -- @exo
  decide

theorem kayak : (perms [0, 1, 2, 1, 0]).eraseDups.length = 30 := by -- @exo
  decide +kernel""",
["`longueur_inserer` et `mem_inserer` : récurrence sur `l`.", "`longueur_perms` : la longueur d'un `flatMap` est la somme des longueurs (`List.length_flatMap`) ; chaque terme vaut `|l| + 1`. `List.map_congr_left` permet de remplacer la fonction par une constante.", "`anna`, `kayak` : des calculs."], "Combinatoire.Menus")

co("Derangements", "Le problème des chapeaux", 2, ["Solutions.Combinatoire.Anagrammes"],
"""`n` personnes déposent leur chapeau au vestiaire ; on les leur rend au hasard. Quelle est la
probabilité que **personne** ne récupère le sien ? Ce sont les **dérangements** (permutations sans
point fixe). Leur nombre vérifie `D(n + 2) = (n + 1)(D(n) + D(n + 1))`, et la probabilité tend vers
`1/e ≈ 0,3679` (Montmort, 1708) — presque indépendamment de `n` !

## À prouver
1. `quatre_cinq` : en comptant pour de vrai, `D(4) = 9` et `D(5) = 44`.
2. `recurrence_ok` : la formule de récurrence donne les bons nombres pour `n ≤ 5`.
3. `un_sur_e` : pour 10 personnes, la probabilité est `0,367…`""",
"""open Parcours.Recurrence

def derangements (n : Nat) : List (List Nat) :=
  (perms (List.range n)).filter fun p => (List.range n).all fun i => p.getD i 0 != i

def der : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (der n + der (n + 1))

theorem quatre_cinq : (derangements 4).length = 9 ∧ (derangements 5).length = 44 := by -- @exo
  decide +kernel

theorem recurrence_ok : ∀ n, n < 6 → (derangements n).length = der n := by -- @exo
  decide +kernel

theorem un_sur_e : der 10 * 1000 / fact 10 = 367 := by -- @exo
  decide""",
["Ce sont des calculs : `decide +kernel`.", "Essaie `#eval derangements 3` pour voir les 2 dérangements de 3 objets."], "Combinatoire.Anagrammes",
ressources=["[Dérangement (Wikipédia)](https://fr.wikipedia.org/wiki/D%C3%A9rangement)"])

co("Catalan", "Les nombres de Catalan", 2, [CB],
"""Combien de façons d'écrire `n` paires de parenthèses bien équilibrées ? `1, 1, 2, 5, 14, 42…` :
les **nombres de Catalan**. Ils comptent aussi les façons de découper un polygone en triangles,
les chemins de Dyck, les arbres binaires… Ils vérifient `C(n + 1) = Σ C(i) C(n − i)` (on coupe à la
parenthèse qui ferme la première), et `C(n) = binom (2n) n / (n + 1)`.

## À prouver
1. `catalan_compte` : pour `n ≤ 5`, le nombre de mots bien parenthésés de longueur `2n` est `C(n)`.
2. `catalan_binom` : `C(n) × (n + 1) = binom (2n) n` pour `n < 15`.
3. `catalan_dix : catalan 10 = 16796`""",
"""/-- Tous les mots de `n` lettres `true` (ouvrante) / `false` (fermante). -/
def motsP : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (motsP n).flatMap fun w => [true :: w, false :: w]

def dyck : List Bool → Nat → Bool
  | [], c => c == 0
  | true :: w, c => dyck w (c + 1)
  | false :: w, c => c != 0 && dyck w (c - 1)

/-- La liste `[C(0), …, C(n)]`, calculée par la récurrence. -/
def catalans : Nat → List Nat
  | 0 => [1]
  | n + 1 =>
    let l := catalans n
    l ++ [((List.range (n + 1)).map fun i => l.getD i 0 * l.getD (n - i) 0).sum]

def catalan (n : Nat) : Nat := (catalans n).getD n 0

theorem catalan_compte : ∀ n, n < 6 → ((motsP (2 * n)).filter (dyck · 0)).length = catalan n := by -- @exo
  decide +kernel

theorem catalan_binom : ∀ n, n < 15 → catalan n * (n + 1) = binom (2 * n) n := by -- @exo
  decide +kernel

theorem catalan_dix : catalan 10 = 16796 := by -- @exo
  decide""",
["Ce sont des calculs : `decide +kernel`.", "`#eval (motsP 6).filter (dyck · 0)` montre les 5 mots pour `n = 3`."], "Combinatoire.CrosseHockey",
ressources=["[Nombre de Catalan (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_de_Catalan)"])

co("Cadenas", "Le cadenas à 4 chiffres", 1, [CD],
"""Un cadenas a 4 molettes de 0 à 9 : `10⁴ = 10 000` codes. Combien ont 4 chiffres **tous
différents** ? `10 × 9 × 8 × 7 = 5040` (10 choix pour le premier, 9 pour le second…).
Donc près de la moitié des codes ont un chiffre répété !

## À prouver
1. `differents : 5040` codes à chiffres distincts,
2. `repetes : 4960` codes avec au moins un chiffre répété.""",
"""def chiffres4 (n : Nat) : List Nat := [n / 1000 % 10, n / 100 % 10, n / 10 % 10, n % 10]

theorem differents :
    ((List.range 10000).filter fun n => (chiffres4 n).eraseDups.length == 4).length = 5040 := by -- @exo
  decide +kernel

theorem repetes :
    ((List.range 10000).filter fun n => (chiffres4 n).eraseDups.length != 4).length = 4960 := by -- @exo
  decide +kernel""",
["Ce sont des calculs sur 10 000 codes : `decide +kernel`."], "Combinatoire.Menus")

pb("Bertrand", "Les boîtes de Bertrand", 1, [PD],
"""Trois boîtes : l'une contient deux pièces d'or, l'autre deux pièces d'argent, la troisième une de
chaque. On choisit une boîte au hasard, on en tire une pièce : elle est en or. Quelle est la
probabilité que l'autre pièce de la boîte soit aussi en or ? Pas 1/2, mais **2/3** !
(Joseph Bertrand, 1889.) Raison : on a plus de chances d'avoir tiré de l'or dans la boîte or-or.

On code un tirage par `(boîte, pièce)`, avec 6 tirages équiprobables, puis on ne garde que ceux où
la pièce tirée est en or.

## À prouver
1. `bertrand` : la probabilité vaut 2/3,
2. `pas_un_demi` : et pas 1/2.""",
"""/-- `true` = or. Boîte 0 : or-or, boîte 1 : or-argent, boîte 2 : argent-argent. -/
def boites : List (List Bool) := [[true, true], [true, false], [false, false]]

def tirages : List (Nat × Nat) := [0, 1, 2].flatMap fun b => [0, 1].map fun p => (b, p)

def orTire (t : Nat × Nat) : Bool := (boites.getD t.1 []).getD t.2 false
def autreOr (t : Nat × Nat) : Bool := (boites.getD t.1 []).getD (1 - t.2) false

theorem bertrand : ProbaEst (tirages.filter orTire) autreOr 2 3 := by -- @exo
  decide

theorem pas_un_demi : ¬ ProbaEst (tirages.filter orTire) autreOr 1 2 := by -- @exo
  decide""",
["`decide` compte les cas."], "Probabilites.DeuxEnfants",
ressources=["[Paradoxe des boîtes de Bertrand (Wikipédia)](https://fr.wikipedia.org/wiki/Paradoxe_des_bo%C3%AEtes_de_Bertrand)"])

pb("Galilee", "Le problème du grand-duc de Toscane", 1, [PD],
"""Vers 1620, le grand-duc de Toscane demande à Galilée : avec trois dés, 9 et 10 s'obtiennent
chacun de 6 façons (`9 = 1+2+6 = 1+3+5 = …`), pourtant 10 sort plus souvent que 9. Pourquoi ?
Galilée répond qu'il faut compter les dés **dans l'ordre** : `1+2+6` correspond à 6 lancers
différents, mais `3+3+3` à un seul. Il y a 27 lancers qui font 10, et 25 qui font 9.

## À prouver
1. `six_et_six` : 9 et 10 ont chacun 6 décompositions (sans ordre).
2. `galilee` : la probabilité de 10 est 27/216, celle de 9 est 25/216.""",
"""def troisDes : List (Nat × Nat × Nat) :=
  de.flatMap fun a => de.flatMap fun b => de.map fun c => (a, b, c)

def total (t : Nat × Nat × Nat) : Nat := t.1 + t.2.1 + t.2.2

/-- Les trois dés rangés dans l'ordre croissant. -/
def ranger (t : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let a := t.1
  let b := t.2.1
  let c := t.2.2
  (min a (min b c), a + b + c - min a (min b c) - max a (max b c), max a (max b c))

theorem six_et_six : ((troisDes.filter (total · == 9)).map ranger).eraseDups.length = 6 ∧
    ((troisDes.filter (total · == 10)).map ranger).eraseDups.length = 6 := by -- @exo
  decide +kernel

theorem galilee : ProbaEst troisDes (total · == 10) 27 216 ∧ ProbaEst troisDes (total · == 9) 25 216 := by -- @exo
  decide +kernel""",
["Ce sont des calculs sur les 216 lancers : `decide +kernel`."], "Probabilites.Des",
ressources=["[Problème du duc de Toscane (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Problem_of_points)"])

pb("Partis", "Le problème des partis", 2, ["Solutions.Probabilites.PileOuFace"],
"""En 1654, le chevalier de Méré pose à Pascal ce problème : deux joueurs misent 32 pistoles
chacun ; le premier à gagner 3 manches (à pile ou face) emporte tout. La partie est interrompue
alors qu'Alice mène 2 à 1. Comment partager équitablement les 64 pistoles ?

Idée de Fermat : imaginer qu'on joue **toujours** 2 manches de plus (même si la partie est finie
avant) ; Alice gagne si elle remporte au moins une des deux : probabilité 3/4. Elle doit donc
recevoir 48 pistoles, Bob 16. La correspondance entre Pascal et Fermat sur ce problème est
considérée comme l'acte de naissance du calcul des probabilités.

## À prouver
1. `partage : ProbaEst (mots 2) (fun w => w.any id) 3 4`
2. `partage_2_3` : s'il manque 2 manches à Alice et 3 à Bob, on joue 4 manches fictives, et Alice
   gagne avec probabilité 11/16.""",
"""theorem partage : ProbaEst (mots 2) (fun w => w.any id) 3 4 := by -- @exo
  decide

theorem partage_2_3 : ProbaEst (mots 4) (fun w => decide (2 ≤ w.count true)) 11 16 := by -- @exo
  decide""",
["`mots n` est la liste des `2ⁿ` suites de pile ou face ; `decide` compte.", "Dans `partage_2_3`, Alice gagne si elle remporte au moins 2 des 4 manches fictives."], "Probabilites.PileOuFace",
ressources=["[Problème des partis (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_des_partis)"])

gr("GrapheComplet", "Le graphe complet", 2, [GD],
"""Dans un tournoi où chacun affronte chacun, avec `n` joueurs, combien de matchs ? C'est le
nombre d'arêtes du **graphe complet** `Kₙ` : `n(n − 1)/2`. On le construit en ajoutant les
sommets un par un : le sommet `n` se relie aux `n` sommets précédents.

## À prouver
1. `aretes_complet : 2 * (complet n).length = n * (n - 1)`
2. `degres_k5` : dans `K₅`, chaque sommet a 4 voisins.""",
"""def complet : Nat → Graphe
  | 0 => []
  | n + 1 => complet n ++ (List.range n).map fun j => (j, n)

theorem aretes_complet (n : Nat) : 2 * (complet n).length = n * (n - 1) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [complet, List.length_append, List.length_map, List.length_range]
    rcases n with _ | k
    · rfl
    · simp only [Nat.add_sub_cancel] at ih ⊢
      grind

theorem degres_k5 : (List.range 5).all (fun v => degre (complet 5) v == 4) = true := by -- @exo
  decide""",
["Récurrence ; `List.length_append`, `List.length_map`, `List.length_range`.", "Pour éviter `n − 1`, sépare `n = 0` et `n = k + 1`, puis `grind`."], "Graphes.PoigneesDeMains")

gr("PereNoel", "La maison du père Noël", 1, [GD],
"""Le jeu d'enfant : dessiner la « maison du père Noël » (un carré avec ses deux diagonales et un
toit) **sans lever le crayon** et sans repasser sur un trait.

```
      4
     / \\
    3---2
    |\\ /|
    | X |
    |/ \\|
    0---1
```
D'après Euler, c'est possible seulement en partant d'un sommet de degré **impair** : ici les deux
coins du bas, 0 et 1.

## À faire
1. Écris `dessin` (la suite des sommets visités) et prouve `dessin_ok`.
2. `impairs` : les sommets de degré impair sont exactement 0 et 1.
3. `compte` : il y a 44 dessins qui partent du coin 0, et aucun qui part du toit.""",
"""def maison : Graphe := [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2), (1, 3), (2, 4), (3, 4)]

def norme (e : Nat × Nat) : Nat × Nat := (min e.1 e.2, max e.1 e.2)

def traits : List Nat → List (Nat × Nat)
  | a :: b :: r => (a, b) :: traits (b :: r)
  | _ => []

def DessinOk (g : Graphe) (d : List Nat) : Bool := ((traits d).map norme).isPerm (g.map norme)

def dessin : List Nat := -- @exo
  [0, 1, 3, 4, 2, 3, 0, 2, 1]

theorem dessin_ok : DessinOk maison dessin = true := by -- @exo
  decide

theorem impairs : (List.range 5).filter (fun v => degre maison v % 2 == 1) = [0, 1] := by -- @exo
  decide

/-- Le nombre de dessins qui partent de `v` en utilisant toutes les arêtes de `g` (`f` : réserve de calcul). -/
def nbDessins : Nat → Graphe → Nat → Nat
  | _, [], _ => 1
  | 0, _, _ => 0
  | f + 1, g, v => ((List.range g.length).map fun i =>
      let e := g.getD i (0, 0)
      if e.1 == v then nbDessins f (g.eraseIdx i) e.2
      else if e.2 == v then nbDessins f (g.eraseIdx i) e.1
      else 0).sum

theorem compte : nbDessins 8 maison 0 = 44 ∧ nbDessins 8 maison 4 = 0 := by -- @exo
  decide +kernel""",
["Pars du coin 0 et essaie de garder le toit pour le milieu du dessin.", "`impairs` et `compte` sont des calculs."], "Graphes.Konigsberg",
ressources=["[Das Haus vom Nikolaus (Wikipédia, en allemand)](https://de.wikipedia.org/wiki/Haus_vom_Nikolaus)"])

cl("Brahmagupta", "Le produit de deux sommes de deux carrés", 1, [AD],
"""`5 = 1² + 2²` et `13 = 2² + 3²`, alors `65 = 5 × 13` est aussi une somme de deux carrés :
`65 = 4² + 7² = 1² + 8²`. C'est toujours vrai, grâce à l'identité de Brahmagupta (VIIᵉ siècle) :
c'est la multiplication des nombres complexes `|z|² |w|² = |zw|²` !""",
"""1. `brahmagupta : (a² + b²)(c² + d²) = (ac − bd)² + (ad + bc)²`
2. `soixante_cinq : 65 = 4 ^ 2 + 7 ^ 2 ∧ 65 = 1 ^ 2 + 8 ^ 2`""",
"""theorem brahmagupta (a b c d : Int) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by -- @exo
  grind

theorem soixante_cinq : (65 : Nat) = 4 ^ 2 + 7 ^ 2 ∧ (65 : Nat) = 1 ^ 2 + 8 ^ 2 := by -- @exo
  decide""",
["`grind` développe les deux côtés."], "Classiques.Pythagore",
ressources=["[Identité de Brahmagupta (Wikipédia)](https://fr.wikipedia.org/wiki/Identit%C3%A9_de_Brahmagupta)"])

cl("QuatreCarres", "L'identité des quatre carrés", 2, [AD],
"""Euler (1748) : le produit de deux sommes de **quatre** carrés est une somme de quatre carrés.
C'est l'étape clé du théorème de Lagrange (« tout entier est somme de quatre carrés ») et, vu
aujourd'hui, la multiplication des **quaternions** de Hamilton.""",
"`quatre_carres` : l'identité d'Euler.",
"""theorem quatre_carres (a b c d x y z w : Int) :
    (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) =
      (a * x - b * y - c * z - d * w) ^ 2 + (a * y + b * x + c * w - d * z) ^ 2 +
      (a * z - b * w + c * x + d * y) ^ 2 + (a * w + b * z - c * y + d * x) ^ 2 := by -- @exo
  grind""",
["`grind` (ça fait beaucoup de termes, mais il s'en sort)."], "Classiques.Brahmagupta",
ressources=["[Identité des quatre carrés d'Euler (Wikipédia)](https://fr.wikipedia.org/wiki/Identit%C3%A9_des_quatre_carr%C3%A9s_d%27Euler)"])

cl("LogDeuxTrois", "log₂ 3 est irrationnel", 2, [RD, "Solutions.Listes.Pont"],
"""Si `log₂ 3 = p/q`, alors `2^p = 3^q`. Impossible : à gauche un nombre pair (si `p ≥ 1`), à droite
un nombre impair. (C'est aussi pourquoi aucune gamme musicale ne tombe juste : 12 quintes
`(3/2)¹²` ne font jamais exactement 7 octaves `2⁷`.)""",
"""1. `trois_pow_impair : 3 ^ b % 2 = 1`
2. `log_deux_trois : 0 < q → 2 ^ p ≠ 3 ^ q`""",
"""theorem trois_pow_impair (b : Nat) : 3 ^ b % 2 = 1 := by -- @exo
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [Nat.pow_succ]
    omega

theorem log_deux_trois (p q : Nat) (hq : 0 < q) : 2 ^ p ≠ 3 ^ q := by -- @exo
  intro h
  have h3 := trois_pow_impair q
  cases p with
  | zero =>
    have : 3 ≤ 3 ^ q := by
      calc 3 = 3 ^ 1 := rfl
        _ ≤ 3 ^ q := Nat.pow_le_pow_right (by omega) hq
    simp at h
    omega
  | succ p =>
    rw [Nat.pow_succ] at h
    omega""",
["`trois_pow_impair` : récurrence, `Nat.pow_succ`, `omega`.", "Pour `p ≥ 1`, `2^p = 2^(p-1) × 2` est pair. Pour `p = 0`, `1 = 3^q ≥ 3` : `Nat.pow_le_pow_right`."], "Classiques.CarrePair",
ressources=["[Comma pythagoricien (Wikipédia)](https://fr.wikipedia.org/wiki/Comma_pythagoricien)"])

cl("TrousPremiers", "Des déserts de nombres premiers", 3, ["Solutions.Arithmetique.InfinitePremiers"],
"""Il y a une infinité de nombres premiers, mais aussi des « déserts » aussi longs qu'on veut :
`(n+1)! + 2, (n+1)! + 3, …, (n+1)! + (n+1)` sont `n` entiers consécutifs **tous composés**,
car `k` divise `(n+1)! + k` pour `2 ≤ k ≤ n + 1`. Par exemple, il existe 1000 entiers consécutifs
dont aucun n'est premier.""",
"""1. `desert : 2 ≤ k → k ≤ n + 1 → ¬ Premier (fact (n + 1) + k)`
2. `mille : ∃ m, ∀ i, i < 1000 → ¬ Premier (m + i)`""",
"""open Parcours.Arith Parcours.Recurrence

theorem desert (n k : Nat) (h1 : 2 ≤ k) (h2 : k ≤ n + 1) : ¬ Premier (fact (n + 1) + k) := by -- @exo
  intro ⟨_, hp⟩
  have hd : k ∣ fact (n + 1) + k := divise_add (divise_fact (by omega) h2) (divise_refl k)
  rcases hp k hd with h | h
  · omega
  · have := fact_pos (n + 1)
    omega

theorem mille : ∃ m, ∀ i, i < 1000 → ¬ Premier (m + i) := by -- @exo
  refine ⟨fact 1001 + 2, fun i hi => ?_⟩
  rw [Nat.add_assoc]
  exact desert 1000 (2 + i) (by omega) (by omega)""",
["`divise_fact : 1 ≤ k → k ≤ n → k ∣ fact n`, et `divise_add`.", "Un premier n'a que 1 et lui-même comme diviseurs ; or `1 < k < (n+1)! + k`.", "Pour `mille` : `m = 1001! + 2`."], "Arithmetique.InfinitePremiers")

cl("FibAddition", "La formule d'addition de Fibonacci", 3, [RD],
"""Pour monter un escalier de `m + n + 1` marches par pas de 1 ou 2 (il y a `F(k+1)` façons pour
`k` marches) : soit on pose le pied sur la marche `m`, soit on l'enjambe (on passe de `m − 1` à
`m + 1`). D'où `F(m + n + 1) = F(m + 1) F(n + 1) + F(m) F(n)`.""",
"""1. `fib_addition : fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n`
2. `fib_double : fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2`""",
"""open Parcours.Recurrence

theorem fib_addition (m n : Nat) :
    fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n := by -- @exo
  induction n using fib.induct with
  | case1 => simp [fib]
  | case2 =>
    simp [fib]
    omega
  | case3 n ih1 ih2 =>
    have h1 : fib (m + (n + 2) + 1) = fib (m + n + 1) + fib (m + (n + 1) + 1) := by
      rw [show m + (n + 2) + 1 = (m + n + 1) + 2 by omega, fib_add_two]
      rfl
    have h2 : fib (n + 1 + 1 + 1) = fib (n + 1) + fib (n + 1 + 1) := fib_add_two (n + 1)
    have h3 : fib (n + 1 + 1) = fib n + fib (n + 1) := fib_add_two n
    show fib (m + (n + 2) + 1) = fib (m + 1) * fib (n + 1 + 1 + 1) + fib m * fib (n + 1 + 1)
    rw [h1, ih1, ih2, h2, h3]
    grind

theorem fib_double (n : Nat) : fib (2 * n + 1) = fib (n + 1) ^ 2 + fib n ^ 2 := by -- @exo
  rw [show 2 * n + 1 = n + n + 1 by omega, fib_addition]
  grind""",
["Récurrence « à la Fibonacci » : `induction n using fib.induct` donne les cas 0, 1 et `n + 2` avec deux hypothèses de récurrence.", "Dans le dernier cas, développe `fib (m + n + 3)` et `fib (n + 3)` avec `fib_add_two`, puis `grind`.", "`fib_double` : prends `m = n`."], "Recurrence.Cassini",
ressources=["[Nombres de Fibonacci (Wikipédia)](https://fr.wikipedia.org/wiki/Suite_de_Fibonacci)"])

cl("Criteres", "Les critères de divisibilité", 1, [RD, "Solutions.Listes.Pont"],
"""Pourquoi suffit-il de regarder le dernier chiffre pour savoir si un nombre est divisible par 2
ou 5 ? Parce que `n = 10 × (n / 10) + (dernier chiffre)` et que 10 est divisible par 2 et 5.
Même idée avec les deux derniers chiffres pour 4 et 25 (`100 = 4 × 25`), et les trois derniers pour 8.""",
"""1. `par_deux : n % 2 = (n % 10) % 2` (et pareil pour 5)
2. `par_quatre : n % 4 = (n % 100) % 4` (et pareil pour 25)
3. `par_huit : n % 8 = (n % 1000) % 8`""",
"""theorem par_deux (n : Nat) : n % 2 = (n % 10) % 2 ∧ n % 5 = (n % 10) % 5 := by -- @exo
  omega

theorem par_quatre (n : Nat) : n % 4 = (n % 100) % 4 ∧ n % 25 = (n % 100) % 25 := by -- @exo
  omega

theorem par_huit (n : Nat) : n % 8 = (n % 1000) % 8 := by -- @exo
  omega""",
["`omega` connaît `%` par une constante."], "Classiques.NeufEtDix")

ecrire_tout()
