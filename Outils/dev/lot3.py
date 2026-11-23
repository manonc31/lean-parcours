import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

NSA = "Parcours.Arith"
exo("Arithmetique", "PgcdProprietes", "Propriétés du PGCD", 3, ["Solutions.Arithmetique.PgcdDivise", "Solutions.Arithmetique.DiviseOrdre"],
 """Le PGCD est **symétrique** (même si l'algorithme d'Euclide ne l'est pas !).

## À prouver
1. `pgcd_comm : pgcd a b = pgcd b a`
2. `pgcd_zero_gauche : pgcd 0 a = a`
3. `pgcd_un : pgcd 1 a = 1`""",
 """theorem pgcd_comm (a b : Nat) : pgcd a b = pgcd b a := by -- @exo
  apply divise_antisymm
  · exact divise_pgcd (pgcd_divise a b).2 (pgcd_divise a b).1
  · exact divise_pgcd (pgcd_divise b a).2 (pgcd_divise b a).1

theorem pgcd_zero_gauche (a : Nat) : pgcd 0 a = a := by -- @exo
  rw [pgcd_comm, pgcd_zero]

theorem pgcd_un (a : Nat) : pgcd 1 a = 1 := by -- @exo
  exact divise_un (pgcd_divise 1 a).1""",
 ["`pgcd_comm` : deux nombres qui se divisent mutuellement sont égaux (`divise_antisymm`). Chaque PGCD divise l'autre, grâce à `divise_pgcd` et `pgcd_divise`."], NSA, requiert="Arithmetique.PgcdDivise")
exo("Arithmetique", "Ppcm", "Le PPCM", 3, ["Solutions.Arithmetique.PgcdDivise"],
 """Le plus petit commun multiple : `ppcm a b = a × b / pgcd a b`. (Les lemmes de division de `Nat`
sont permis : `Nat.mul_div_cancel'`, `Nat.mul_div_assoc`.)

## À prouver
1. `pgcd_mul_ppcm : pgcd a b * ppcm a b = a * b`
2. `divise_ppcm : a ∣ ppcm a b`""",
 """def ppcm (a b : Nat) : Nat := a * b / pgcd a b

theorem pgcd_mul_ppcm (a b : Nat) : pgcd a b * ppcm a b = a * b := by -- @exo
  unfold ppcm
  exact Nat.mul_div_cancel' (divise_mul_droite (pgcd_divise a b).1 b)

theorem divise_ppcm (a b : Nat) : a ∣ ppcm a b := by -- @exo
  unfold ppcm
  rw [Nat.mul_div_assoc a (pgcd_divise a b).2]
  exact ⟨b / pgcd a b, rfl⟩""",
 ["`Nat.mul_div_cancel' (h : n ∣ m) : n * (m / n) = m`. Il faut donc montrer que `pgcd a b` divise `a * b`.", "`Nat.mul_div_assoc a (h : k ∣ b) : a * b / k = a * (b / k)`."], NSA, requiert="Arithmetique.PgcdMul")
exo("Arithmetique", "Deux", "Le premier des premiers", 2, ["Solutions.Arithmetique.DiviseOrdre"],
 """`2` est premier, et c'est le seul premier pair.

## À prouver
1. `premier_deux : Premier 2`
2. `premier_impair : Premier p → p ≠ 2 → p % 2 = 1`""",
 """theorem premier_deux : Premier 2 := by -- @exo
  refine ⟨Nat.le_refl 2, fun d hd => ?_⟩
  have hle := divise_le hd (by decide)
  have hd0 : d ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hd
    omega
  omega

theorem premier_impair {p : Nat} (hp : Premier p) (h2 : p ≠ 2) : p % 2 = 1 := by -- @exo
  apply Classical.byContradiction
  intro h
  rcases hp.2 2 ⟨p / 2, by omega⟩ with h' | h' <;> omega""",
 ["`premier_deux` : un diviseur `d` de 2 vérifie `d ≤ 2` (`divise_le`) et `d ≠ 0`. `omega` conclut `d = 1 ∨ d = 2`.", "`premier_impair` : si `p` est pair, `2 ∣ p` (témoin `p / 2`), donc `2 = 1` ou `2 = p`."], NSA, requiert="Arithmetique.FacteurPremier")
exo("Arithmetique", "TestPrimalite", "Un test de primalité prouvé", 4, ["Solutions.Arithmetique.DiviseOrdre"],
 """`estPremier n` teste tous les diviseurs possibles (un algorithme lent, mais correct). Prouve qu'il
répond exactement `Premier n`. En récompense : `decide` peut maintenant prouver que 97 est premier !

## À prouver
1. `estPremier_correct : estPremier n = true ↔ Premier n`
2. `premier_97 : Premier 97`""",
 """def estPremier (n : Nat) : Bool := 2 ≤ n && (List.range n).all (fun d => d < 2 || n % d != 0)

theorem estPremier_correct (n : Nat) : estPremier n = true ↔ Premier n := by -- @exo
  unfold estPremier
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, hall⟩
    refine ⟨h2, fun d hd => ?_⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hd
      omega
    have hle := divise_le hd (by omega)
    apply Classical.byContradiction
    intro hne
    obtain ⟨k, hk⟩ := hd
    rcases hall d (by omega) with h | h
    · omega
    · apply h
      rw [hk]
      exact Nat.mul_mod_right d k
  · rintro ⟨h2, hp⟩
    refine ⟨h2, fun d _ => ?_⟩
    apply Classical.byContradiction
    intro hne
    have hd2 : 2 ≤ d := by omega
    have hmod : n % d = 0 := by omega
    have hdiv : d ∣ n := ⟨n / d, by have := Nat.div_add_mod n d; omega⟩
    rcases hp d hdiv with h | h <;> omega

theorem premier_97 : Premier 97 := by -- @exo
  exact (estPremier_correct 97).mp (by decide)""",
 ["Déplie et simplifie : `simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq]`.",
  "Sens `→` : un diviseur `d` de `n` qui n'est ni 1 ni `n` vérifierait `2 ≤ d < n` et `n % d = 0` (`Nat.mul_mod_right`).",
  "Sens `←` : si `n % d = 0` avec `2 ≤ d < n`, alors `d ∣ n` (témoin `n / d`, avec `Nat.div_add_mod`), contradiction.",
  "`premier_97` : `(estPremier_correct 97).mp (by decide)`."], NSA, requiert="Arithmetique.Deux")
exo("Arithmetique", "SommeDeuxCarres", "Somme de deux carrés modulo 4", 2, ["Solutions.Arithmetique.Definitions"],
 """Une somme de deux carrés n'est jamais de la forme `4k + 3`. Donc `3, 7, 11, 19, 23…` ne sont pas sommes
de deux carrés. (Fermat a montré que pour les premiers, c'est même une équivalence : voir le boss des deux carrés.)

## À prouver
`somme_deux_carres (a b : Nat) : (a * a + b * b) % 4 ≠ 3`""",
 """theorem somme_deux_carres (a b : Nat) : (a * a + b * b) % 4 ≠ 3 := by -- @exo
  have carre : ∀ z : Nat, z * z % 4 = 0 ∨ z * z % 4 = 1 := by
    intro z
    have : z % 4 = 0 ∨ z % 4 = 1 ∨ z % 4 = 2 ∨ z % 4 = 3 := by omega
    rcases this with hz | hz | hz | hz <;> simp [Nat.mul_mod, hz]
  have ha := carre a
  have hb := carre b
  omega""",
 ["Un carré vaut 0 ou 1 modulo 4 (quatre cas sur le reste, `Nat.mul_mod`).", "Puis `omega`."], NSA, requiert="Arithmetique.Congruences")

NSC = "Parcours.Combi"
exo("Combinatoire", "Chemins", "Chemins dans une grille", 3, ["Solutions.Combinatoire.BinomBase"],
 """Combien de chemins pour aller du coin `(0, 0)` au coin `(m, n)` d'une grille, en ne faisant que des pas
vers la droite ou vers le haut ? `chemins m n` les compte récursivement (le dernier pas vient de la gauche
ou d'en bas). La réponse : `C(m + n, m)`, on choisit les positions des `m` pas vers la droite.

## À prouver
`chemins_binom (m n : Nat) : chemins m n = binom (m + n) m`""",
 """def chemins : Nat → Nat → Nat
  | 0, _ => 1
  | _, 0 => 1
  | m + 1, n + 1 => chemins m (n + 1) + chemins (m + 1) n

theorem chemins_binom (m n : Nat) : chemins m n = binom (m + n) m := by -- @exo
  induction m generalizing n with
  | zero => simp [chemins, binom_zero_droite]
  | succ m ih =>
    induction n with
    | zero => simp [chemins, binom_self]
    | succ n ihn =>
      simp only [chemins]
      rw [ih (n + 1), ihn, show m + 1 + (n + 1) = (m + n + 1) + 1 by omega, binom_succ_succ,
        show m + (n + 1) = m + n + 1 by omega, show m + 1 + n = m + n + 1 by omega]""",
 ["Double récurrence : sur `m` (en généralisant `n`), puis sur `n`.", "Cas récursif : déplie avec `simp only [chemins]`, applique les deux hypothèses de récurrence, puis la formule de Pascal `binom_succ_succ`. Ajuste les sommes d'indices avec `show … by omega`."], NSC, requiert="Combinatoire.BinomBase")
exo("Combinatoire", "DeuxParmi", "Combien de poignées de main ?", 3, ["Solutions.Combinatoire.BinomBase"],
 """Dans un groupe de `n` personnes, si chacun serre la main de chacun, il y a `C(n, 2) = n(n−1)/2` poignées
de main. Sans division : `2 × C(n, 2) = n(n − 1)`.

## À prouver
`deux_parmi (n : Nat) : 2 * binom n 2 = n * (n - 1)`""",
 """theorem deux_parmi (n : Nat) : 2 * binom n 2 = n * (n - 1) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [binom_succ_succ, binom_un, Nat.mul_add, ih, Nat.add_sub_cancel]
    cases n with
    | zero => rfl
    | succ k =>
      rw [Nat.add_sub_cancel]
      grind""",
 ["Récurrence. `binom (n + 1) 2 = binom n 1 + binom n 2 = n + binom n 2` (`binom_succ_succ`, `binom_un`).", "Il reste un calcul avec une soustraction : sépare `n = 0` et `n = k + 1`, puis `grind`."], NSC, requiert="Combinatoire.BinomBase")

NSP = "Parcours.Proba"
exo("Probabilites", "Mere", "Le paradoxe du chevalier de Méré", 1, ["Solutions.Probabilites.Definitions"],
 """En 1654, le chevalier de Méré, joueur, remarque :
- parier sur « au moins un 6 en 4 lancers d'un dé » est **gagnant** à long terme ;
- parier sur « au moins un double 6 en 24 lancers de deux dés » est **perdant**…
alors que son raisonnement (faux) lui disait que c'était pareil. Il pose la question à Pascal, qui en
discute avec Fermat : la théorie des probabilités est née !

- P(aucun 6 en 4 lancers) = `(5/6)⁴ < 1/2`, soit `2 × 5⁴ < 6⁴`.
- P(aucun double 6 en 24 lancers) = `(35/36)²⁴ > 1/2`, soit `36²⁴ < 2 × 35²⁴`.

Et pour finir : une grille de Loto (5 numéros parmi 49, plus un numéro chance parmi 10) a une chance
sur 19 068 840 de gagner.

## À prouver
1. `mere_un_de : 2 * 5 ^ 4 < 6 ^ 4`
2. `mere_deux_des : 36 ^ 24 < 2 * 35 ^ 24`
3. `loto : fact 49 / (fact 5 * fact 44) * 10 = 19068840`""",
 """theorem mere_un_de : 2 * 5 ^ 4 < 6 ^ 4 := by -- @exo
  decide

theorem mere_deux_des : 36 ^ 24 < 2 * 35 ^ 24 := by -- @exo
  decide

theorem loto : Parcours.Recurrence.fact 49 / (Parcours.Recurrence.fact 5 * Parcours.Recurrence.fact 44) * 10 = 19068840 := by -- @exo
  decide""",
 ["Ce sont des calculs : `decide`.", "Mais prends le temps de comprendre pourquoi ces inégalités traduisent les probabilités !"], NSP, requiert="Probabilites.Des")
exo("Probabilites", "Efron", "Les dés non transitifs d'Efron", 2, ["Solutions.Probabilites.Definitions"],
 """Quatre dés étranges :
- A : `4 4 4 4 0 0` ;
- B : `3 3 3 3 3 3` ;
- C : `6 6 2 2 2 2` ;
- D : `5 5 5 1 1 1`.

A bat B deux fois sur trois, B bat C deux fois sur trois, C bat D deux fois sur trois… et **D bat A**
deux fois sur trois ! « Être plus fort que » n'est pas transitif. (Bradley Efron, 1970 ; Warren Buffett
aurait proposé ce jeu à Bill Gates, qui a flairé le piège et laissé Buffett choisir son dé en premier.)

## À prouver
`efron` : les quatre duels sont gagnés avec probabilité 2/3.""",
 """def deA : List Nat := [4, 4, 4, 4, 0, 0]
def deB : List Nat := [3, 3, 3, 3, 3, 3]
def deC : List Nat := [6, 6, 2, 2, 2, 2]
def deD : List Nat := [5, 5, 5, 1, 1, 1]

/-- Toutes les issues d'un duel entre deux dés. -/
def duel (x y : List Nat) : List (Nat × Nat) := x.flatMap (fun a => y.map (fun b => (a, b)))

def gagne (p : Nat × Nat) : Bool := decide (p.2 < p.1)

theorem efron : ProbaEst (duel deA deB) gagne 2 3 ∧ ProbaEst (duel deB deC) gagne 2 3 ∧
    ProbaEst (duel deC deD) gagne 2 3 ∧ ProbaEst (duel deD deA) gagne 2 3 := by -- @exo
  decide""",
 ["Un calcul sur 4 × 36 issues : `decide`."], NSP, requiert="Probabilites.Des")

NSE = "Parcours.Enigmes"
exo("Enigmes", "Escalier", "Monter un escalier", 3, ["Solutions.Recurrence.Definitions", "Solutions.Listes.Pont"],
 """On monte un escalier de `n` marches, une ou deux marches à la fois. De combien de façons ?
`montees n` les énumère toutes : la première enjambée fait 1 ou 2 marches. Réponse : le nombre de
Fibonacci `F(n + 1)` ! (C'est le problème qui a fait découvrir la suite… à des poètes indiens du VIᵉ
siècle, qui comptaient les rythmes de syllabes longues et brèves.)

## À prouver
1. `nombre_montees : (montees n).length = fib (n + 1)`
2. `somme_montees : ∀ l ∈ montees n, l.sum = n` (chaque montée fait bien `n` marches)""",
 """open Parcours.Recurrence

def montees : Nat → List (List Nat)
  | 0 => [[]]
  | 1 => [[1]]
  | n + 2 => (montees (n + 1)).map (1 :: ·) ++ (montees n).map (2 :: ·)

theorem nombre_montees (n : Nat) : (montees n).length = fib (n + 1) := by -- @exo
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | n + 2 =>
      simp only [montees, List.length_append, List.length_map]
      rw [ih (n + 1) (by omega), ih n (by omega), show n + 2 + 1 = (n + 1) + 2 from rfl, fib_add_two (n + 1)]
      omega

theorem somme_montees (n : Nat) : ∀ l ∈ montees n, l.sum = n := by -- @exo
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => simp [montees]
    | 1 => simp [montees]
    | n + 2 =>
      intro l hl
      simp only [montees, List.mem_append, List.mem_map] at hl
      rcases hl with ⟨l', hl', rfl⟩ | ⟨l', hl', rfl⟩
      · simp only [List.sum_cons, ih (n + 1) (by omega) l' hl']
        omega
      · simp only [List.sum_cons, ih n (by omega) l' hl']
        omega""",
 ["Récurrence forte (`Nat.strongRecOn`), avec `match n with | 0 | 1 | n + 2`.", "Pour le nombre : `List.length_append`, `List.length_map`, puis `fib_add_two`.", "Pour la somme : `List.mem_append`, `List.mem_map` décomposent l'appartenance ; `List.sum_cons`."], NSE, requiert="Recurrence.Fibonacci")
exo("Enigmes", "Diophante", "L'épitaphe de Diophante", 2, ["Solutions.Recurrence.Definitions"],
 """« Passant, sous ce tombeau repose Diophante. Ces quelques vers vont te dire la durée de sa vie.
Son enfance en a occupé la sixième partie ; puis sa barbe a poussé pendant un douzième ; il se maria
après un septième, et cinq ans plus tard il eut un fils. Mais ce fils mourut à la moitié de l'âge
qu'atteignit son père, qui lui survécut quatre ans. »

En notant `x` l'âge de Diophante (multiple de 84 pour que toutes les fractions soient entières) :
`x/6 + x/12 + x/7 + 5 + x/2 + 4 = x`.

## À prouver
`diophante (h84 : x % 84 = 0) (h : x / 6 + x / 12 + x / 7 + 5 + x / 2 + 4 = x) : x = 84`""",
 """theorem diophante (x : Nat) (h84 : x % 84 = 0) (h : x / 6 + x / 12 + x / 7 + 5 + x / 2 + 4 = x) :
    x = 84 := by -- @exo
  omega""",
 ["`omega` sait gérer les divisions par des constantes !", "À la main : écris `x = 84k` ; l'équation devient `75k + 9 = 84k`."], NSE, requiert="Gymnase.Omega")
exo("Enigmes", "SendMoreMoney", "SEND + MORE = MONEY", 2, ["Solutions.Recurrence.Definitions", "Solutions.Listes.Pont"],
 """Le cryptarithme le plus célèbre (Henry Dudeney, 1924) : chaque lettre est un chiffre différent,
et `SEND + MORE = MONEY`. Trouve la solution (unique) et fais-la vérifier par Lean.

## À prouver
`send_more_money : ∃ s e n d m o r y, (tous différents) ∧ (chiffres) ∧ s ≠ 0 ∧ m ≠ 0 ∧ SEND + MORE = MONEY`""",
 """/-- La valeur d'un nombre écrit avec la liste de ses chiffres. -/
def nombre (l : List Nat) : Nat := l.foldl (fun acc c => 10 * acc + c) 0

theorem send_more_money : ∃ s e n d m o r y : Nat,
    [s, e, n, d, m, o, r, y].Nodup ∧ (∀ x ∈ [s, e, n, d, m, o, r, y], x < 10) ∧ s ≠ 0 ∧ m ≠ 0 ∧
    nombre [s, e, n, d] + nombre [m, o, r, e] = nombre [m, o, n, e, y] := by -- @exo
  exact ⟨9, 5, 6, 7, 1, 0, 8, 2, by decide⟩""",
 ["`M` est forcément 1 (une retenue), donc `S` vaut 8 ou 9…", "La solution : `9567 + 1085 = 10652`. Donne-la avec `exact ⟨9, 5, 6, 7, 1, 0, 8, 2, by decide⟩`."], NSE, requiert="Enigmes.Chevaliers")

NSI = "Parcours.Info"
exo("Informatique", "Typage", "Les programmes bien typés ne plantent pas", 4, ["Solutions.Informatique.Expressions"],
 """Un petit langage avec des entiers, des booléens, `+`, `si … alors … sinon` et `=`. Certaines expressions
n'ont pas de sens (`vrai + 3`) : l'évaluation échoue (`none`). Un **système de types** les rejette
avant l'exécution. Le théorème de **sûreté** : une expression bien typée s'évalue toujours, et donne
une valeur du bon type.

Robin Milner (1978) : *« Well-typed programs cannot go wrong. »* C'est la promesse des langages typés
(OCaml, Haskell, Rust… et Lean).

## À prouver
`surete : ATy e t → ∃ v, eval e = some v ∧ v.aType t`

## Ressources
- [Sûreté du typage (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Type_safety)""",
 """inductive Ty where
  | nat
  | bool

inductive Exp where
  | num (k : Nat)
  | vrai
  | faux
  | plus (e₁ e₂ : Exp)
  | si (c e₁ e₂ : Exp)
  | egal (e₁ e₂ : Exp)

inductive Val where
  | n (k : Nat)
  | b (v : Bool)

def Exp.eval : Exp → Option Val
  | .num k => some (.n k)
  | .vrai => some (.b true)
  | .faux => some (.b false)
  | .plus e₁ e₂ =>
    match e₁.eval, e₂.eval with
    | some (.n a), some (.n b) => some (.n (a + b))
    | _, _ => none
  | .si c e₁ e₂ =>
    match c.eval with
    | some (.b true) => e₁.eval
    | some (.b false) => e₂.eval
    | _ => none
  | .egal e₁ e₂ =>
    match e₁.eval, e₂.eval with
    | some (.n a), some (.n b) => some (.b (a == b))
    | _, _ => none

/-- `ATy e t` : l'expression `e` a le type `t`. -/
inductive ATy : Exp → Ty → Prop
  | num (k : Nat) : ATy (.num k) .nat
  | vrai : ATy .vrai .bool
  | faux : ATy .faux .bool
  | plus {e₁ e₂ : Exp} : ATy e₁ .nat → ATy e₂ .nat → ATy (.plus e₁ e₂) .nat
  | si {c e₁ e₂ : Exp} {t : Ty} : ATy c .bool → ATy e₁ t → ATy e₂ t → ATy (.si c e₁ e₂) t
  | egal {e₁ e₂ : Exp} : ATy e₁ .nat → ATy e₂ .nat → ATy (.egal e₁ e₂) .bool

/-- Une valeur a-t-elle un type donné ? -/
def Val.aType : Val → Ty → Prop
  | .n _, .nat => True
  | .b _, .bool => True
  | _, _ => False

theorem surete {e : Exp} {t : Ty} (h : ATy e t) : ∃ v, e.eval = some v ∧ v.aType t := by -- @exo
  induction h with
  | num k => exact ⟨.n k, rfl, trivial⟩
  | vrai => exact ⟨.b true, rfl, trivial⟩
  | faux => exact ⟨.b false, rfl, trivial⟩
  | plus _ _ ih₁ ih₂ =>
    obtain ⟨v₁, h₁, t₁⟩ := ih₁
    obtain ⟨v₂, h₂, t₂⟩ := ih₂
    cases v₁ with
    | b _ => exact False.elim t₁
    | n a =>
      cases v₂ with
      | b _ => exact False.elim t₂
      | n b => exact ⟨.n (a + b), by simp [Exp.eval, h₁, h₂], trivial⟩
  | si _ _ _ ihc ih₁ ih₂ =>
    obtain ⟨vc, hc, tc⟩ := ihc
    cases vc with
    | n _ => exact False.elim tc
    | b bv =>
      cases bv
      · obtain ⟨v, hv, tv⟩ := ih₂
        exact ⟨v, by simp [Exp.eval, hc, hv], tv⟩
      · obtain ⟨v, hv, tv⟩ := ih₁
        exact ⟨v, by simp [Exp.eval, hc, hv], tv⟩
  | egal _ _ ih₁ ih₂ =>
    obtain ⟨v₁, h₁, t₁⟩ := ih₁
    obtain ⟨v₂, h₂, t₂⟩ := ih₂
    cases v₁ with
    | b _ => exact False.elim t₁
    | n a =>
      cases v₂ with
      | b _ => exact False.elim t₂
      | n b => exact ⟨.b (a == b), by simp [Exp.eval, h₁, h₂], trivial⟩""",
 ["Récurrence sur la dérivation de typage (`induction h with`).",
  "Pour `plus` : les hypothèses de récurrence donnent deux valeurs de type `nat`. Fais `cases` sur ces valeurs : le cas booléen est impossible (`False.elim t₁`, car `Val.aType (.b _) .nat` est `False`).",
  "Pour calculer `eval` : `simp [Exp.eval, h₁, h₂]`."], NSI, requiert="Informatique.Expressions")

NSAl = "Parcours.Algebre"
exo("Algebre", "OrdreElement", "Puissances et ordre d'un élément", 2, ["Solutions.Algebre.Puissances"],
 """Si `aⁿ = 1`, alors toutes les puissances `a^(n·k)` valent aussi 1. (Le plus petit tel `n > 0` s'appelle
l'**ordre** de `a`.)

## À prouver
1. `un_puiss : (1 : G) ^ k = 1`
2. `puiss_mul : a ^ (m * n) = (a ^ m) ^ n`
3. `puiss_ordre : a ^ n = 1 → a ^ (n * k) = 1`""",
 """variable {G : Type} [Groupe G]

theorem un_puiss (k : Nat) : (1 : G) ^ k = 1 := by -- @exo
  induction k with
  | zero => rfl
  | succ k ih => rw [puiss_succ, ih, Groupe.one_mul]

theorem puiss_mul (a : G) (m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, puiss_add, ih, puiss_succ]

theorem puiss_ordre {a : G} {n : Nat} (h : a ^ n = 1) (k : Nat) : a ^ (n * k) = 1 := by -- @exo
  rw [puiss_mul, h, un_puiss]""",
 ["Récurrences sur l'exposant, avec `puiss_succ` et `puiss_add`.", "`puiss_ordre` se déduit des deux premiers."], NSAl, requiert="Algebre.Puissances")
exo("Algebre", "CarreProduit", "Le carré d'un produit", 3, ["Solutions.Algebre.Inverses"],
 """Dans un groupe, `(ab)² = a²b²` si et seulement si `a` et `b` **commutent**. (Dans un groupe non
commutatif, l'identité `(ab)² = a²b²` est donc fausse en général !)

## À prouver
`carre_produit : a * b * (a * b) = a * a * (b * b) ↔ a * b = b * a`""",
 """variable {G : Type} [Groupe G]

theorem carre_produit (a b : G) : a * b * (a * b) = a * a * (b * b) ↔ a * b = b * a := by -- @exo
  have simpl_droite : ∀ x y z : G, x * z = y * z → x = y := by
    intro x y z h
    calc x = x * z * z⁻¹ := by rw [Groupe.mul_assoc, mul_inv, mul_one]
      _ = y * z * z⁻¹ := by rw [h]
      _ = y := by rw [Groupe.mul_assoc, mul_inv, mul_one]
  constructor
  · intro h
    rw [Groupe.mul_assoc, Groupe.mul_assoc a a] at h
    have h2 := mul_gauche_simpl h
    rw [← Groupe.mul_assoc, ← Groupe.mul_assoc a b b] at h2
    exact (simpl_droite _ _ _ h2).symm
  · intro h
    rw [Groupe.mul_assoc, ← Groupe.mul_assoc b a b, ← h, Groupe.mul_assoc a b b, ← Groupe.mul_assoc]""",
 ["Sens `→` : réassocie pour faire apparaître `a * (…)` des deux côtés, simplifie par `a` à gauche (`mul_gauche_simpl`), puis par `b` à droite.",
  "Pour simplifier à droite, prouve d'abord `x * z = y * z → x = y` (multiplie par `z⁻¹`).",
  "Sens `←` : réécris `b * a` en `a * b` au bon endroit (`← h`) et réassocie."], NSAl, requiert="Algebre.Inverses")

NSJ = "Parcours.Jeux"
exo("Jeux", "FortBoyard", "Les bâtonnets de Fort Boyard", 3, ["Solutions.Recurrence.Definitions"],
 """À Fort Boyard, on retire 1, 2 ou 3 bâtonnets, et celui qui prend le **dernier** a **perdu** (version
« misère » du Nim). Les positions perdantes deviennent celles où le nombre de bâtonnets vaut 1 modulo 4.
Le maître du temps laisse donc toujours `4k + 1` bâtonnets à son adversaire…

`gagnanteMisere n` : avec `n` bâtonnets, le joueur au trait peut-il forcer la victoire ?
(Avec 0 bâtonnet, l'adversaire vient de prendre le dernier : il a perdu, on a gagné.)

## À prouver
`fort_boyard (n : Nat) : gagnanteMisere n = (n % 4 != 1)`

## Ressources
- [Fort Boyard, les bâtonnets (Wikipédia)](https://fr.wikipedia.org/wiki/Jeux_de_Nim)""",
 """def gagnanteMisere : Nat → Bool
  | 0 => true
  | 1 => false
  | 2 => true
  | n + 3 => !gagnanteMisere (n + 2) || !gagnanteMisere (n + 1) || !gagnanteMisere n

theorem fort_boyard (n : Nat) : gagnanteMisere n = (n % 4 != 1) := by -- @exo
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 =>
      simp only [gagnanteMisere]
      rw [ih (n + 2) (by omega), ih (n + 1) (by omega), ih n (by omega)]
      have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
      rcases this with h | h | h | h <;> simp [h, Nat.add_mod]""",
 ["Même méthode que pour le Nim à un tas : récurrence forte, trois cas de base, puis un calcul modulo 4."], NSJ, requiert="Jeux.Nim")

ecrire_tout()
