import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

RD = "Solutions.Recurrence.Definitions"
LP = "Solutions.Listes.Pont"
AD = "Solutions.Arithmetique.Definitions"
PD = "Solutions.Probabilites.Definitions"
CD = "Solutions.Combinatoire.Definitions"

exo("Jeux", "Jeu15", "Le jeu de 15", 1, [LP, RD],
"""Deux joueurs choisissent à tour de rôle un nombre de 1 à 9 (chacun une seule fois). Le premier
qui possède **trois nombres dont la somme fait 15** a gagné. Ce jeu semble difficile… mais c'est un
**morpion déguisé** ! Dans le carré magique de Lo Shu, les triplets de somme 15 sont exactement les
8 lignes, colonnes et diagonales.
```
2 7 6
9 5 1
4 3 8
```

## À prouver
1. `huit_triplets` : il y a exactement 8 triplets de nombres distincts de 1 à 9 de somme 15.
2. `morpion` : chacun est une ligne du carré magique (et réciproquement).""",
"""def triplets15 : List (List Nat) :=
  (List.range 10).flatMap fun a => (List.range 10).flatMap fun b => (List.range 10).filterMap fun c =>
    if 0 < a ∧ a < b ∧ b < c ∧ a + b + c = 15 then some [a, b, c] else none

def loShu : List Nat := [2, 7, 6, 9, 5, 1, 4, 3, 8]

def lignesMorpion : List (List Nat) :=
  [[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8], [0, 4, 8], [2, 4, 6]]

def lignesLoShu : List (List Nat) := lignesMorpion.map fun l => l.map (loShu.getD · 0)

theorem huit_triplets : triplets15.length = 8 := by -- @exo
  decide

theorem morpion : (∀ t ∈ triplets15, ∃ l ∈ lignesLoShu, t.isPerm l = true) ∧
    (∀ l ∈ lignesLoShu, ∃ t ∈ triplets15, t.isPerm l = true) := by -- @exo
  decide""",
["Tout se vérifie par le calcul : `decide`."], "Parcours.Jeux", requiert="Enigmes.CarreMagique",
ressources=["[Isomorphisme du jeu de 15 et du morpion (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Number_Scrabble)"])

exo("Probabilites", "Simpson", "Le paradoxe de Simpson", 1, [PD],
"""Une étude médicale (1986) compare deux traitements des calculs rénaux :

| | petits calculs | gros calculs | total |
|---|---|---|---|
| Traitement A | 81/87 guéris | 192/263 | 273/350 |
| Traitement B | 234/270 | 55/80 | 289/350 |

A fait **mieux** que B pour les petits calculs, **mieux** pour les gros… mais **moins bien** au
total ! Explication : A a surtout été donné pour les cas difficiles (gros calculs). Méfiance avec
les moyennes !

`meilleur a b c d` signifie `a/b > c/d` (produit en croix).

## À prouver
`petits`, `gros`, `total_simpson`.""",
"""abbrev meilleur (a b c d : Nat) : Prop := c * b < a * d

theorem petits : meilleur 81 87 234 270 := by -- @exo
  decide

theorem gros : meilleur 192 263 55 80 := by -- @exo
  decide

theorem total_simpson : meilleur 289 350 273 350 := by -- @exo
  decide""",
["`decide`."], "Parcours.Proba", requiert="Probabilites.DeuxEnfants",
ressources=["[Paradoxe de Simpson (Wikipédia)](https://fr.wikipedia.org/wiki/Paradoxe_de_Simpson)"])

exo("Probabilites", "Depistage", "Les faux positifs", 1, [PD],
"""Une maladie touche 1 % de la population. Un test la détecte dans 99 % des cas, et se trompe
chez 5 % des personnes saines. Ton test est positif : quelle est la probabilité que tu sois malade ?
Pas 99 % … mais **1 sur 6** environ !

## Se le représenter
Sur 10 000 personnes : 100 malades, dont 99 testés positifs ; 9 900 saines, dont 495 positives.
Parmi les 594 positifs, seuls 99 sont malades : `99/594 = 1/6`. (C'est la formule de Bayes.)

Chaque personne est un couple `(malade, positif)`.

## À prouver
`un_sur_six : ProbaEst (population.filter (·.2)) (·.1) 1 6`""",
"""def population : List (Bool × Bool) :=
  List.replicate 99 (true, true) ++ List.replicate 1 (true, false) ++
  List.replicate 495 (false, true) ++ List.replicate 9405 (false, false)

theorem taille : population.length = 10000 := by -- @exo
  decide +kernel

theorem un_sur_six : ProbaEst (population.filter (·.2)) (·.1) 1 6 := by -- @exo
  decide +kernel""",
["Des calculs sur 10 000 personnes : `decide +kernel`."], "Parcours.Proba", requiert="Probabilites.Simpson",
ressources=["[Théorème de Bayes (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Bayes)"])

exo("Combinatoire", "SansDeuxUns", "Pas deux 1 de suite", 3, [CD],
"""Combien de mots binaires de longueur `n` n'ont **jamais deux 1 consécutifs** ? `1, 2, 3, 5, 8,
13…` : les nombres de Fibonacci ! Un tel mot commence par `0` (suivi d'un bon mot de longueur
`n − 1`) ou par `10` (suivi d'un bon mot de longueur `n − 2`).

## À prouver
1. `nombre : (sans11 n).length = fib (n + 2)`
2. `tous_bons` : tous les mots construits n'ont pas deux 1 consécutifs.
3. `tous_la` : pour `n ≤ 10`, on les a tous (en comparant avec tous les mots).""",
"""open Parcours.Recurrence

def sans11 : Nat → List (List Bool)
  | 0 => [[]]
  | 1 => [[false], [true]]
  | n + 2 => (sans11 (n + 1)).map (false :: ·) ++ (sans11 n).map (fun w => true :: false :: w)

def pasDeuxUns : List Bool → Bool
  | [] => true
  | false :: w => pasDeuxUns w
  | [true] => true
  | true :: false :: w => pasDeuxUns w
  | true :: true :: _ => false

def tousMots : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (tousMots n).flatMap fun w => [false :: w, true :: w]

theorem nombre (n : Nat) : (sans11 n).length = fib (n + 2) := by -- @exo
  induction n using sans11.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 n ih1 ih2 =>
    simp only [sans11, List.length_append, List.length_map, ih1, ih2]
    rw [fib_add_two (n + 2), show n + 2 + 1 = n + 1 + 2 from rfl]
    omega

theorem tous_bons (n : Nat) : ∀ w ∈ sans11 n, pasDeuxUns w = true := by -- @exo
  induction n using sans11.induct with
  | case1 => simp [sans11, pasDeuxUns]
  | case2 => simp [sans11, pasDeuxUns]
  | case3 n ih1 ih2 =>
    intro w hw
    simp only [sans11, List.mem_append, List.mem_map] at hw
    rcases hw with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · simp only [pasDeuxUns]
      exact ih1 v hv
    · simp only [pasDeuxUns]
      exact ih2 v hv

theorem tous_la : ∀ n, n < 11 → ((tousMots n).filter pasDeuxUns).length = (sans11 n).length := by -- @exo
  decide +kernel""",
["`induction n using sans11.induct` donne trois cas (0, 1 et `n + 2`) avec deux hypothèses de récurrence.", "`fib (n + 4) = fib (n + 2) + fib (n + 3)`.", "`tous_bons` : un mot de `sans11 (n + 2)` est `false :: v` ou `true :: false :: v`."], "Parcours.Combi", requiert="Combinatoire.Catalan")

NA = "Parcours.Arith"
exo("Arithmetique", "Parfaits", "Nombres parfaits et amicaux", 1, [AD],
"""Un nombre est **parfait** s'il est égal à la somme de ses diviseurs stricts : `6 = 1 + 2 + 3`,
`28 = 1 + 2 + 4 + 7 + 14`. Les Grecs n'en connaissaient que quatre : 6, 28, 496, 8128. Tous sont de
la forme `2^(p−1) × (2^p − 1)` (Euclide). On ne sait toujours pas s'il existe un parfait impair !

`220` et `284` sont **amicaux** : chacun est la somme des diviseurs stricts de l'autre.

## À prouver
1. `quatre_parfaits`, `pas_d_autre` (sous 100 : seulement 6 et 28)
2. `amicaux`
3. `forme_euclide`""",
"""def diviseursStricts (n : Nat) : List Nat := (List.range n).filter fun d => 0 < d && n % d == 0

def parfait (n : Nat) : Bool := 0 < n && (diviseursStricts n).sum == n

theorem quatre_parfaits : parfait 6 && parfait 28 && parfait 496 && parfait 8128 = true := by -- @exo
  decide +kernel

theorem pas_d_autre : (List.range 100).filter parfait = [6, 28] := by -- @exo
  decide +kernel

theorem amicaux : (diviseursStricts 220).sum = 284 ∧ (diviseursStricts 284).sum = 220 := by -- @exo
  decide

theorem forme_euclide : 6 = 2 ^ 1 * (2 ^ 2 - 1) ∧ 28 = 2 ^ 2 * (2 ^ 3 - 1) ∧
    496 = 2 ^ 4 * (2 ^ 5 - 1) ∧ 8128 = 2 ^ 6 * (2 ^ 7 - 1) := by -- @exo
  decide""",
["Des calculs : `decide` / `decide +kernel`."], NA, requiert="Arithmetique.DiviseBase",
ressources=["[Nombre parfait (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_parfait)"])

exo("Arithmetique", "Fermat5", "Fermat s'est trompé", 1, [AD],
"""Pierre de Fermat avait conjecturé (1640) que tous les nombres `Fₙ = 2^(2ⁿ) + 1` sont premiers :
3, 5, 17, 257, 65537… En 1732, Euler trouve que `F₅ = 4 294 967 297 = 641 × 6 700 417`.
On ne connaît aujourd'hui **aucun** autre nombre de Fermat premier.

## À prouver
1. `valeurs` : `F₀` à `F₄`.
2. `euler : fermat 5 = 641 * 6700417`
3. `astuce` : pourquoi 641 ? Car `641 = 5 × 2⁷ + 1 = 5⁴ + 2⁴`.""",
"""def fermat (n : Nat) : Nat := 2 ^ (2 ^ n) + 1

theorem valeurs : fermat 0 = 3 ∧ fermat 1 = 5 ∧ fermat 2 = 17 ∧ fermat 3 = 257 ∧ fermat 4 = 65537 := by -- @exo
  decide

theorem euler : fermat 5 = 641 * 6700417 := by -- @exo
  decide

theorem astuce : 641 = 5 * 2 ^ 7 + 1 ∧ 641 = 5 ^ 4 + 2 ^ 4 := by -- @exo
  decide""",
["`decide` sait calculer avec de grands nombres."], NA, requiert="Arithmetique.Parfaits",
ressources=["[Nombre de Fermat (Wikipédia)](https://fr.wikipedia.org/wiki/Nombre_de_Fermat)"])

NC = "Parcours.Classiques"
exo("Classiques", "Ramanujan", "Le taxi de Ramanujan", 1, [LP, RD],
"""Le mathématicien Hardy rend visite à Ramanujan à l'hôpital, en taxi n°1729 : « un nombre plutôt
ennuyeux ». Ramanujan répond aussitôt : « Non, c'est un nombre très intéressant : c'est le plus
petit nombre qui s'écrit de deux façons différentes comme somme de deux cubes ! »
`1729 = 1³ + 12³ = 9³ + 10³`.

## À prouver
1. `deux_facons`
2. `plus_petit` : les sommes de deux cubes plus petites que 1729 sont toutes différentes (pour
   `n < 1729`, les cubes utiles sont au plus `12³ = 1728`).""",
"""/-- Toutes les sommes `a³ + b³` avec `a ≤ b ≤ 12`. -/
def sommesCubes : List Nat :=
  (List.range 13).flatMap fun a => ((List.range 13).filter fun b => a ≤ b).map fun b => a ^ 3 + b ^ 3

theorem deux_facons : 1729 = 1 ^ 3 + 12 ^ 3 ∧ 1729 = 9 ^ 3 + 10 ^ 3 ∧ sommesCubes.count 1729 = 2 := by -- @exo
  decide

theorem plus_petit : (sommesCubes.filter (· < 1729)).Nodup := by -- @exo
  decide +kernel""",
["`decide` / `decide +kernel`."], NC, requiert="Classiques.Pythagore",
ressources=["[1729 (nombre) (Wikipédia)](https://fr.wikipedia.org/wiki/1729_(nombre))"])

exo("Classiques", "Annee2025", "2025, une année remarquable", 1, [LP, RD],
"""2025 est un carré : `45²`. C'est aussi un nombre de Kaprekar : `20 + 25 = 45`. Et
`2025 = (1 + 2 + ⋯ + 9)² = 1³ + 2³ + ⋯ + 9³` (Nicomaque !). La prochaine année carrée sera 2116.

## À prouver
`carre`, `kaprekar`, `nicomaque`, et `prochaine` (aucun carré entre 2025 et 2116).""",
"""theorem carre : 2025 = 45 ^ 2 := by -- @exo
  decide

theorem kaprekar : 2025 / 100 + 2025 % 100 = 45 := by -- @exo
  decide

theorem nicomaque : ((List.range 10).sum) ^ 2 = 2025 ∧ ((List.range 10).map (· ^ 3)).sum = 2025 := by -- @exo
  decide

theorem prochaine : 2116 = 46 ^ 2 ∧ ∀ k, k < 100 → k ^ 2 ≤ 2025 ∨ 2116 ≤ k ^ 2 := by -- @exo
  decide""",
["Des calculs : `decide`."], NC, requiert="Recurrence.Cubes")

exo("Algebre", "Horloge", "L'arithmétique de l'horloge", 1, [LP, RD],
"""Sur une horloge, `9 h + 5 h = 2 h` : on calcule **modulo 12**. Dans ce monde, certains nombres ont
un inverse (`5 × 5 = 25 = 2 × 12 + 1`, donc `5⁻¹ = 5`), d'autres non (3, 4, 6…). Et il y a des
« diviseurs de zéro » : `3 × 4 = 0` ! Modulo un nombre premier comme 7, tout nombre non nul est
inversible : c'est un **corps**.

## À prouver
1. `neuf_plus_cinq`
2. `inversibles_douze : inversibles = [1, 5, 7, 11]` et chacun est son propre inverse.
3. `diviseurs_de_zero : 3 * 4 % 12 = 0`
4. `corps_sept` : modulo 7, tout `a ≠ 0` a un inverse.""",
"""def inversibles : List Nat := (List.range 12).filter fun a => (List.range 12).any fun b => a * b % 12 == 1

theorem neuf_plus_cinq : (9 + 5) % 12 = 2 := by -- @exo
  decide

theorem inversibles_douze : inversibles = [1, 5, 7, 11] ∧ ∀ a ∈ inversibles, a * a % 12 = 1 := by -- @exo
  decide

theorem diviseurs_de_zero : 3 * 4 % 12 = 0 := by -- @exo
  decide

theorem corps_sept : ∀ a, a < 7 → 0 < a → ∃ b, b < 7 ∧ a * b % 7 = 1 := by -- @exo
  decide""",
["`decide` essaie toutes les valeurs."], "Parcours.Algebre", requiert="Algebre.Anneaux",
ressources=["[Arithmétique modulaire (Wikipédia)](https://fr.wikipedia.org/wiki/Arithm%C3%A9tique_modulaire)"])

NI = "Parcours.Info"
exo("Informatique", "RSA", "RSA en miniature", 2, [LP, RD],
"""RSA (Rivest, Shamir, Adleman, 1977) protège tes paiements en ligne. Version jouet : `p = 61`,
`q = 53`, `n = pq = 3233`. La clé publique est `e = 17`, la clé secrète `d = 2753`, avec
`e × d ≡ 1 (mod (p − 1)(q − 1))`. Chiffrer `m`, c'est calculer `mᵉ mod n` ; déchiffrer, `cᵈ mod n`.
Le miracle (petit théorème de Fermat) : on retrouve toujours `m`.

Pour calculer vite, on utilise l'exponentiation rapide modulaire (avec une réserve de calcul).

## À prouver
1. `cles : 61 * 53 = 3233 ∧ 17 * 2753 % (60 * 52) = 1`
2. `exemple` : le message 65 est chiffré en 2790, qui se déchiffre en 65.
3. `rsa` : **tous** les messages `m < 3233` se déchiffrent correctement (on les vérifie par
   paquets de 100, pour ne pas essouffler le noyau de Lean).""",
"""/-- `puissMod f a k m = a^k mod m`, par exponentiation rapide (`f` : réserve de calcul). -/
def puissMod : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m => 1 % m
  | f + 1, a, k, m =>
    if k = 0 then 1 % m
    else
      let r := puissMod f a (k / 2) m
      if k % 2 = 0 then r * r % m else r * r * a % m

def chiffrer (m : Nat) : Nat := puissMod 20 m 17 3233
def dechiffrer (c : Nat) : Nat := puissMod 20 c 2753 3233

theorem cles : 61 * 53 = 3233 ∧ 17 * 2753 % (60 * 52) = 1 := by -- @exo
  decide

theorem exemple : chiffrer 65 = 2790 ∧ dechiffrer 2790 = 65 := by -- @exo
  decide

theorem par_centaines : ∀ k, k < 33 → ∀ j, j < 100 → 100 * k + j < 3233 →
    dechiffrer (chiffrer (100 * k + j)) = 100 * k + j := by -- @exo
  decide +kernel

theorem rsa (m : Nat) (h : m < 3233) : dechiffrer (chiffrer m) = m := by -- @exo
  have := par_centaines (m / 100) (by omega) (m % 100) (Nat.mod_lt _ (by decide)) (by omega)
  rwa [Nat.div_add_mod] at this""",
["Des calculs : `decide +kernel` vérifie les 3233 messages.", "Pour la preuve générale (pour tous `p`, `q`), il faudrait le petit théorème de Fermat et le lemme chinois : voir la branche Arithmétique !"], NI, requiert="Programmes.ExpModulaire",
ressources=["[Chiffrement RSA (Wikipédia)](https://fr.wikipedia.org/wiki/Chiffrement_RSA)"])

exo("Informatique", "Hamming", "Le code correcteur de Hamming", 2, [LP, RD],
"""Comment une sonde spatiale ou une barrette de mémoire corrige-t-elle les erreurs de transmission ?
Le **code de Hamming** (1950) ajoute 3 bits de contrôle à 4 bits de données. Si **un** bit (n'importe
lequel des 7) est inversé pendant le transport, le récepteur le repère et le corrige : le
« syndrome » (3 bits de parité recalculés) donne directement la position de l'erreur !

## À prouver
1. `corrige_une_erreur` : pour les 16 messages et les 8 situations (aucune erreur ou une erreur à
   l'une des 7 positions), on retrouve le message.
2. `deux_erreurs` : avec deux erreurs, le code peut se tromper.""",
"""def encoderH (d : List Bool) : List Bool :=
  let d1 := d.getD 0 false
  let d2 := d.getD 1 false
  let d3 := d.getD 2 false
  let d4 := d.getD 3 false
  [d1 ^^ d2 ^^ d4, d1 ^^ d3 ^^ d4, d1, d2 ^^ d3 ^^ d4, d2, d3, d4]

/-- La position de l'erreur (de 1 à 7), ou 0 s'il n'y en a pas. -/
def syndrome (c : List Bool) : Nat :=
  let b := fun i => c.getD (i - 1) false
  (b 1 ^^ b 3 ^^ b 5 ^^ b 7).toNat + 2 * (b 2 ^^ b 3 ^^ b 6 ^^ b 7).toNat +
    4 * (b 4 ^^ b 5 ^^ b 6 ^^ b 7).toNat

/-- Inverse le bit en position `i` (de 1 à 7) ; `i = 0` : ne fait rien. -/
def inverser (c : List Bool) (i : Nat) : List Bool :=
  if i = 0 then c else c.set (i - 1) (!(c.getD (i - 1) false))

def decoderH (c : List Bool) : List Bool :=
  let c' := inverser c (syndrome c)
  [c'.getD 2 false, c'.getD 4 false, c'.getD 5 false, c'.getD 6 false]

def messages : List (List Bool) :=
  [false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c =>
    [false, true].map fun d => [a, b, c, d]

theorem corrige_une_erreur : ∀ d ∈ messages, ∀ i, i < 8 → decoderH (inverser (encoderH d) i) = d := by -- @exo
  decide

theorem deux_erreurs : ∃ d ∈ messages, decoderH (inverser (inverser (encoderH d) 1) 2) ≠ d := by -- @exo
  decide""",
["Des vérifications exhaustives : `decide`.", "Pourquoi ça marche : chaque position `i` (écrite en binaire) dit exactement quels bits de contrôle elle influence."], NI, requiert="Circuits.Gray",
ressources=["[Code de Hamming (Wikipédia)](https://fr.wikipedia.org/wiki/Code_de_Hamming)"])

ecrire_tout()
