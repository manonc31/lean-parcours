import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

P = "Solutions.Programmes.Definitions"
RD = "Solutions.Recurrence.Definitions"
LP = "Solutions.Listes.Pont"

def pr(ident, titre, diff, texte, code, indices, requiert, imports=(P,), ressources=()):
    exo("Programmes", ident, titre, diff, list(imports), texte, code, indices, "Parcours.Prog", requiert=requiert, ressources=ressources)

pr("BoyerMoore", "Le vote majoritaire de Boyer-Moore", 4,
"""Comment trouver l'élément **majoritaire** d'une liste (présent plus d'une fois sur deux) en un
seul passage et avec une mémoire minuscule ? L'algorithme de Boyer et Moore (1981) garde un
**candidat** et un **compteur** : un élément égal au candidat fait monter le compteur, un élément
différent le fait baisser (il « annule » une voix du candidat) ; à 0, on change de candidat.

## L'invariant
Pour chaque valeur `x`, note `bal x` = (nombre de `x`) − (nombre d'autres éléments) dans la partie
déjà lue. Alors à tout moment : `bal x ≤ k` si `x` est le candidat, et `bal x ≤ −k` sinon.
À la fin, si `m` est majoritaire, `bal m > 0`, donc `m` est forcément le candidat !

## À prouver
1. `pas_inv` : un pas de l'algorithme préserve l'invariant.
2. `bal_cons`, `bm_inv` : l'invariant à la fin.
3. `majorite : l.length < 2 * l.count m → (bm l c 0).1 = m`""",
"""def pasBM (c k y : Nat) : Nat × Nat :=
  if k = 0 then (y, 1) else if c = y then (c, k + 1) else (c, k - 1)

def bm : List Nat → Nat → Nat → Nat × Nat
  | [], c, k => (c, k)
  | y :: l, c, k => bm l (pasBM c k y).1 (pasBM c k y).2

def bal (x : Nat) (l : List Nat) : Int := 2 * (l.count x : Int) - l.length

def borne (c k x : Nat) : Int := if c = x then (k : Int) else -(k : Int)

theorem pas_inv (c k y x : Nat) (B : Int) (h : B ≤ borne c k x) :
    B + (if y = x then 1 else -1) ≤ borne (pasBM c k y).1 (pasBM c k y).2 x := by -- @exo
  unfold borne pasBM at *
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte] at h ⊢
    by_cases hyx : y = x <;> simp only [hyx, ↓reduceIte] <;> split at h <;> omega
  · simp only [hk, ↓reduceIte]
    by_cases hcy : c = y
    · subst hcy
      by_cases hcx : c = x <;> simp only [hcx, ↓reduceIte] at h ⊢ <;> omega
    · simp only [hcy, ↓reduceIte]
      by_cases hcx : c = x <;> by_cases hyx : y = x <;> simp only [hcx, hyx, ↓reduceIte] at h ⊢ <;> omega

theorem bal_cons (x y : Nat) (l : List Nat) : bal x (y :: l) = bal x l + (if y = x then 1 else -1) := by -- @exo
  unfold bal
  rw [List.count_cons, List.length_cons]
  by_cases h : y = x <;> simp [h] <;> omega

theorem bm_inv (l : List Nat) : ∀ (c k x : Nat) (B : Int), B ≤ borne c k x →
    B + bal x l ≤ borne (bm l c k).1 (bm l c k).2 x := by -- @exo
  induction l with
  | nil =>
    intro c k x B h
    simpa [bm, bal] using h
  | cons y l ih =>
    intro c k x B h
    have := ih (pasBM c k y).1 (pasBM c k y).2 x _ (pas_inv c k y x B h)
    rw [bal_cons]
    simp only [bm]
    omega

theorem majorite (l : List Nat) (m c : Nat) (h : l.length < 2 * l.count m) : (bm l c 0).1 = m := by -- @exo
  have := bm_inv l c 0 m 0 (by simp [borne])
  unfold bal borne at this
  by_cases hne : (bm l c 0).1 = m
  · exact hne
  · simp only [hne, ↓reduceIte] at this
    omega""",
["`pas_inv` : beaucoup de cas (compteur nul ou non, candidat égal à `y` ou non, `x` égal au candidat ou à `y`…) ; dans chacun, `simp only [h…, ↓reduceIte]` puis `omega`.", "`bm_inv` : récurrence sur `l` en généralisant tout ; la borne de départ `B` absorbe ce qui a déjà été lu.", "`majorite` : applique `bm_inv` avec `B = 0` et un compteur nul au départ."], "Programmes.Compter",
ressources=["[Algorithme de vote à la majorité de Boyer-Moore (Wikipédia)](https://fr.wikipedia.org/wiki/Algorithme_de_vote_%C3%A0_la_majorit%C3%A9_de_Boyer-Moore)"])

pr("Motif", "Chercher un mot dans un texte", 3,
"""Le Ctrl+F de ton éditeur : chercher la première position où un motif apparaît dans un texte.
Version naïve : on essaie chaque position, et on regarde si le texte **commence par** le motif.

## À prouver
1. `commencePar_spec : commencePar m t = true ↔ m <+: t` (`<+:` : « est un préfixe de »)
2. `trouve_correct` : si on trouve la position `j`, le motif est bien là.
3. `absent_correct` : si on ne trouve rien, le motif n'apparaît nulle part.
4. `exemple_motif : chercherMotif [1, 2] [3, 1, 1, 2, 5] 0 = some 2`""",
"""def commencePar : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: m, b :: t => a == b && commencePar m t

/-- `chercherMotif m t i` : première position (comptée à partir de `i`) où `m` apparaît dans `t`. -/
def chercherMotif (m : List Nat) : List Nat → Nat → Option Nat
  | [], i => if m.isEmpty then some i else none
  | b :: t, i => if commencePar m (b :: t) then some i else chercherMotif m t (i + 1)

theorem commencePar_spec (m t : List Nat) : commencePar m t = true ↔ m <+: t := by -- @exo
  induction m generalizing t with
  | nil => simp [commencePar, List.nil_prefix]
  | cons a m ih =>
    cases t with
    | nil => simp [commencePar]
    | cons b t => simp [commencePar, ih, List.cons_prefix_cons]

theorem trouve_correct (m t : List Nat) (i j : Nat) (h : chercherMotif m t i = some j) :
    i ≤ j ∧ m <+: t.drop (j - i) := by -- @exo
  induction t generalizing i with
  | nil =>
    simp only [chercherMotif] at h
    split at h
    · rename_i hm
      cases h
      simp only [List.isEmpty_iff] at hm
      subst hm
      simp
    · simp at h
  | cons b t ih =>
    simp only [chercherMotif] at h
    split at h
    · rename_i hc
      cases h
      simpa using (commencePar_spec m (b :: t)).mp hc
    · obtain ⟨h1, h2⟩ := ih (i + 1) h
      refine ⟨by omega, ?_⟩
      rw [show j - i = (j - (i + 1)) + 1 by omega]
      simpa using h2

theorem absent_correct (m t : List Nat) (i : Nat) (h : chercherMotif m t i = none) :
    ∀ k, ¬ m <+: t.drop k := by -- @exo
  induction t generalizing i with
  | nil =>
    simp only [chercherMotif] at h
    split at h
    · simp at h
    · rename_i hm
      intro k hk
      simp only [List.drop_nil, List.prefix_nil] at hk
      subst hk
      simp at hm
  | cons b t ih =>
    simp only [chercherMotif] at h
    split at h
    · simp at h
    · rename_i hc
      intro k hk
      cases k with
      | zero => exact hc ((commencePar_spec m (b :: t)).mpr (by simpa using hk))
      | succ k => exact ih (i + 1) h k (by simpa using hk)

theorem exemple_motif : chercherMotif [1, 2] [3, 1, 1, 2, 5] 0 = some 2 := by -- @exo
  decide""",
["`commencePar_spec` : récurrence sur le motif, puis `cases t` ; `List.cons_prefix_cons`.", "Les deux autres : récurrence sur le texte en généralisant la position `i`, et `split at h` pour le `if`.", "`(b :: t).drop (k + 1) = t.drop k`."], "Programmes.Recherche",
ressources=["[Algorithme de recherche de sous-chaîne (Wikipédia)](https://fr.wikipedia.org/wiki/Algorithme_de_recherche_de_sous-cha%C3%AEne)"])

pr("RacineNumerique", "La racine numérique", 3,
"""On additionne les chiffres d'un nombre, puis ceux du résultat, etc., jusqu'à obtenir un seul
chiffre : `9875 → 29 → 11 → 2`. C'est la **racine numérique**. Grâce à la preuve par neuf, on peut
la calculer d'un coup : c'est `1 + (n − 1) mod 9` (pour `n > 0`).

On réutilise `sommeChiffres` et `somme_chiffres_mod_neuf` de l'énigme « La preuve par neuf ».

## À prouver
1. `sommeChiffres_le`, `sommeChiffres_lt`, `sommeChiffres_pos` : de quoi justifier que le
   programme s'arrête.
2. `racineNum_spec : racineNum n = if n = 0 then 0 else 1 + (n - 1) % 9`""",
"""open Parcours.Enigmes

theorem sommeChiffres_le (n : Nat) : sommeChiffres n ≤ n := by -- @exo
  fun_induction sommeChiffres n <;> omega

theorem sommeChiffres_lt (n : Nat) (h : 10 ≤ n) : sommeChiffres n < n := by -- @exo
  rw [sommeChiffres]
  have := sommeChiffres_le (n / 10)
  split <;> omega

theorem sommeChiffres_pos (n : Nat) (h : 0 < n) : 0 < sommeChiffres n := by -- @exo
  fun_induction sommeChiffres n with
  | case1 n _ => exact h
  | case2 n h' ih =>
    by_cases h0 : n % 10 = 0
    · have := ih (by omega)
      omega
    · omega

def racineNum (n : Nat) : Nat := if h : n < 10 then n else racineNum (sommeChiffres n)
termination_by n
decreasing_by exact sommeChiffres_lt n (by omega)

theorem racineNum_spec (n : Nat) : racineNum n = if n = 0 then 0 else 1 + (n - 1) % 9 := by -- @exo
  fun_induction racineNum n with
  | case1 n h =>
    split <;> omega
  | case2 n h ih =>
    have h9 := somme_chiffres_mod_neuf n
    have hp := sommeChiffres_pos n (by omega)
    rw [ih]
    simp only [show sommeChiffres n ≠ 0 by omega, show n ≠ 0 by omega, ↓reduceIte]
    omega""",
["`sommeChiffres_le` : `fun_induction`, puis `omega`.", "Pour `racineNum_spec` : `fun_induction racineNum n` ; dans le cas récursif, `sommeChiffres n` et `n` ont le même reste modulo 9, et `sommeChiffres n > 0`."], "Enigmes.PreuveParNeuf", imports=(P, "Solutions.Enigmes.PreuveParNeuf"),
ressources=["[Racine numérique (Wikipédia)](https://fr.wikipedia.org/wiki/Racine_num%C3%A9rique)"])

NI = "Parcours.Info"
exo("Informatique", "MultiplesTrois", "L'automate des multiples de 3", 2, ["Solutions.Informatique.Automates"],
"""Un automate qui lit un nombre écrit en binaire (bit de poids fort en premier) et dit s'il est
multiple de 3, avec seulement **3 états** : le reste modulo 3 de ce qui a été lu. Lire un bit `b`
fait passer de la valeur `v` à `2v + b`, donc du reste `e` au reste `(2e + b) mod 3`.

## À prouver
1. `lire_mod` : après avoir lu `w`, l'automate est dans l'état « valeur de `w` modulo 3 ».
2. `multiple3_correct : multiple3.accepte w = (valeurBin w 0 % 3 == 0)`
3. `neuf : multiple3.accepte [true, false, false, true] = true` (1001 = 9)""",
"""/-- La valeur d'un mot binaire, bit de poids fort en premier (`v` : valeur déjà lue). -/
def valeurBin : List Bool → Nat → Nat
  | [], v => v
  | b :: w, v => valeurBin w (2 * v + b.toNat)

def multiple3 : Automate Nat Bool := ⟨0, fun e b => (2 * e + b.toNat) % 3, fun e => e == 0⟩

theorem lire_mod (w : List Bool) (e v : Nat) (h : e = v % 3) :
    multiple3.lire e w = valeurBin w v % 3 := by -- @exo
  induction w generalizing e v with
  | nil => simp [Automate.lire, valeurBin, h]
  | cons b w ih =>
    simp only [Automate.lire, valeurBin]
    apply ih
    simp only [multiple3]
    omega

theorem multiple3_correct (w : List Bool) : multiple3.accepte w = (valeurBin w 0 % 3 == 0) := by -- @exo
  unfold Automate.accepte
  rw [show multiple3.init = 0 from rfl, lire_mod w 0 0 rfl]
  rfl

theorem neuf : multiple3.accepte [true, false, false, true] = true := by -- @exo
  decide""",
["`lire_mod` : récurrence sur `w` en généralisant l'état `e` et la valeur `v`.", "Le pas : `(2 (v mod 3) + b) mod 3 = (2v + b) mod 3` : `omega`."], NI, requiert="Informatique.Automates")

exo("Informatique", "Castor", "Le castor affairé", 2, [LP, RD],
"""Parmi toutes les machines de Turing à `n` états qui **s'arrêtent** (en partant d'un ruban vide),
laquelle écrit le plus de `1` ? C'est le problème du **castor affairé** (Tibor Radó, 1962). Pour
2 états, le champion écrit 4 uns en 6 étapes ; pour 3 états, 6 uns. Pour 5 états, la réponse
(47 176 870 étapes) n'a été prouvée qu'en 2024… en Coq, un cousin de Lean ! Pour 6 états, le
problème est hors de portée : la fonction du castor affairé grandit plus vite que toute fonction
calculable.

## À prouver
1. `castor_deux` : la machine à 2 états s'arrête après 6 étapes avec 4 uns.
2. `castor_trois` : une machine à 3 états qui écrit 6 uns en 14 étapes.
3. `castor_trois_lent` : une autre qui s'arrête après 21 étapes (le record de durée pour 3 états).""",
"""structure Regle where
  ecrit : Bool
  versDroite : Bool
  suivant : Nat

/-- Une machine : (état, symbole lu) ↦ règle. L'état 0 est l'arrêt. -/
abbrev Machine := Nat → Bool → Regle

structure Config where
  etat : Nat
  gauche : List Bool
  tete : Bool
  droite : List Bool

def unPas (M : Machine) (c : Config) : Config :=
  let r := M c.etat c.tete
  if r.versDroite then ⟨r.suivant, r.ecrit :: c.gauche, c.droite.headD false, c.droite.tail⟩
  else ⟨r.suivant, c.gauche.tail, c.gauche.headD false, r.ecrit :: c.droite⟩

/-- Nombre d'étapes et configuration finale (si la machine s'arrête avant `f` étapes). -/
def executer (M : Machine) : Nat → Config → Option (Nat × Config)
  | 0, _ => none
  | f + 1, c => if c.etat = 0 then some (0, c) else (executer M f (unPas M c)).map fun r => (r.1 + 1, r.2)

def nbUns (c : Config) : Nat := c.gauche.count true + c.tete.toNat + c.droite.count true

def ruban : Config := ⟨1, [], false, []⟩

def bilan (M : Machine) : Option (Nat × Nat) := (executer M 100 ruban).map fun r => (r.1, nbUns r.2)

def castor2 : Machine
  | 1, false => ⟨true, true, 2⟩
  | 1, true => ⟨true, false, 2⟩
  | 2, false => ⟨true, false, 1⟩
  | 2, true => ⟨true, true, 0⟩
  | _, _ => ⟨false, true, 0⟩

def castor3 : Machine
  | 1, false => ⟨true, true, 2⟩
  | 1, true => ⟨true, true, 0⟩
  | 2, false => ⟨false, true, 3⟩
  | 2, true => ⟨true, true, 2⟩
  | 3, false => ⟨true, false, 3⟩
  | 3, true => ⟨true, false, 1⟩
  | _, _ => ⟨false, true, 0⟩

def castor3lent : Machine
  | 1, false => ⟨true, true, 2⟩
  | 1, true => ⟨true, true, 0⟩
  | 2, false => ⟨true, false, 2⟩
  | 2, true => ⟨false, true, 3⟩
  | 3, false => ⟨true, false, 3⟩
  | 3, true => ⟨true, false, 1⟩
  | _, _ => ⟨false, true, 0⟩

theorem castor_deux : bilan castor2 = some (6, 4) := by -- @exo
  decide

theorem castor_trois : bilan castor3 = some (14, 6) := by -- @exo
  decide

theorem castor_trois_lent : bilan castor3lent = some (21, 5) := by -- @exo
  decide""",
["Des simulations : `decide`.", "Essaie `#eval executer castor2 3 ruban |>.map (·.1)` pour suivre la machine pas à pas."], NI, requiert="Informatique.Arret",
ressources=["[Castor affairé (Wikipédia)](https://fr.wikipedia.org/wiki/Castor_affair%C3%A9)", "[Le projet bbchallenge (BB(5), 2024)](https://bbchallenge.org/)"])

NE = "Parcours.Enigmes"
exo("Enigmes", "Curiosites", "Curiosités du calcul", 1, [RD],
"""Quelques calculs étonnants :
- `37 × 3 = 111`, `37 × 6 = 222`, …, `37 × 27 = 999` ;
- `12345679 × 9 = 111111111` (sans le 8 !) ;
- `111111111² = 12345678987654321` ;
- `1089 × 9 = 9801` et `2178 × 4 = 8712` : le produit est le nombre **retourné**.

On peut les vérifier un par un par le calcul (`decide`)… mais pour « 37 × 3k = 111k » on peut
aussi prouver la règle **générale**, pour tout `k`.

## À prouver
`trente_sept`, `trente_sept_general`, `repunit_carre`, `sans_huit`, `retournes`.""",
"""theorem trente_sept : ∀ k, k < 10 → 37 * (3 * k) = 111 * k := by -- @exo
  decide

theorem trente_sept_general (k : Nat) : 37 * (3 * k) = 111 * k := by -- @exo
  omega

theorem repunit_carre : 111111111 * 111111111 = 12345678987654321 := by -- @exo
  decide

theorem sans_huit : 12345679 * 9 = 111111111 := by -- @exo
  decide

theorem retournes : 1089 * 9 = 9801 ∧ 2178 * 4 = 8712 := by -- @exo
  decide""",
["Pour les calculs : `decide`. Pour la règle générale : `omega`."], NE, requiert="Enigmes.Nombre1089")

exo("Enigmes", "NombrePense", "Les tours du nombre pensé", 1, [RD],
"""« Pense à un nombre. Multiplie-le par 2, ajoute 10, divise par 2, et retire le nombre de
départ : tu trouves 5 ! » Le magicien n'a aucun mérite : c'est une identité algébrique.

Autre tour : « Écris un nombre de 3 chiffres deux fois de suite (`abcabc`), divise par 7, puis
par 11, puis par 13 : tu retrouves ton nombre ! » Car `abcabc = 1001 × abc` et `1001 = 7 × 11 × 13`.

## À prouver
1. `toujours_cinq : (2 * n + 10) / 2 - n = 5`
2. `retour : (3 * n + 6) / 3 - 2 = n`
3. `abcabc : n < 1000 → (1000 * n + n) / 7 / 11 / 13 = n`""",
"""theorem toujours_cinq (n : Nat) : (2 * n + 10) / 2 - n = 5 := by -- @exo
  omega

theorem retour (n : Nat) : (3 * n + 6) / 3 - 2 = n := by -- @exo
  omega

theorem abcabc (n : Nat) (h : n < 1000) : (1000 * n + n) / 7 / 11 / 13 = n := by -- @exo
  omega""",
["`omega` connaît la division par une constante."], NE, requiert="Enigmes.PoulesLapins")

ecrire_tout()
