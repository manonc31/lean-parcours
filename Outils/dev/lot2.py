import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

NSN = "Parcours.ℕ"
exo("Naturels", "OrdreMul", "Ordre et multiplication", 2, ["Solutions.Naturels.LeBase", "Solutions.Naturels.MulAdd"],
 """La multiplication respecte l'ordre : si `a ≤ b`, alors `c × a ≤ c × b`.

## À prouver
1. `le_add_right : a ≤ a + b`
2. `mul_le_mul_left : a ≤ b → c * a ≤ c * b`""",
 """theorem le_add_right (a b : ℕ) : a ≤ a + b := by -- @exo
  exact ⟨b, rfl⟩

theorem mul_le_mul_left (a b c : ℕ) (h : a ≤ b) : c * a ≤ c * b := by -- @exo
  obtain ⟨d, rfl⟩ := h
  exact ⟨c * d, mul_add c a d⟩""",
 ["`le_add_right` : le témoin est `b`, et c'est vrai par définition.", "`mul_le_mul_left` : de `b = a + d`, on a `c * b = c * a + c * d` (`mul_add`)."], NSN, requiert="Naturels.LeAdd")
exo("Naturels", "StrictTrans", "Transitivité de <", 2, ["Solutions.Naturels.LeBase"],
 """Rappel : `a < b` signifie `succ a ≤ b`.

## À prouver
1. `lt_succ_self : a < succ a`
2. `lt_of_lt_of_le : a < b → b ≤ c → a < c`
3. `lt_trans : a < b → b < c → a < c`""",
 """theorem lt_succ_self (a : ℕ) : a < succ a := by -- @exo
  exact le_refl (succ a)

theorem lt_of_lt_of_le {a b c : ℕ} (h1 : a < b) (h2 : b ≤ c) : a < c := by -- @exo
  exact le_trans _ _ _ h1 h2

theorem lt_trans {a b c : ℕ} (h1 : a < b) (h2 : b < c) : a < c := by -- @exo
  exact le_trans _ _ _ h1 (le_trans _ _ _ (le_succ_self b) h2)""",
 ["`a < succ a` signifie `succ a ≤ succ a` : `le_refl`.", "Pour `lt_trans` : `succ a ≤ b ≤ succ b ≤ c` (`le_succ_self`, `le_trans`)."], NSN, requiert="Naturels.Strict")
exo("Naturels", "PuissanceNonNulle", "Une puissance non nulle", 2, ["Solutions.Naturels.PowBase", "Solutions.Naturels.MulEqZero"],
 """Si `a ≠ 0`, alors `aⁿ ≠ 0`.

## À prouver
`pow_ne_zero (a n : ℕ) (ha : a ≠ 0) : a ^ n ≠ 0`""",
 """theorem pow_ne_zero (a n : ℕ) (ha : a ≠ 0) : a ^ n ≠ 0 := by -- @exo
  induction n with
  | zero =>
    rw [pow_zero, one_eq_succ_zero]
    exact succ_ne_zero 0
  | succ n ih =>
    intro h
    rw [pow_succ] at h
    rcases mul_eq_zero _ _ h with h1 | h1
    · exact ih h1
    · exact ha h1""",
 ["Récurrence sur `n`. Cas `zero` : `a ^ 0 = 1 = succ 0 ≠ 0`.", "Cas `succ` : `aⁿ⁺¹ = aⁿ × a = 0` donnerait `aⁿ = 0` ou `a = 0` (`mul_eq_zero`)."], NSN, requiert="Naturels.PowBase")
exo("Naturels", "SommeImpairs", "La somme des impairs, à la main", 3, ["Solutions.Naturels.AddMul"],
 """`1 + 3 + 5 + ⋯ + (2n − 1) = n²`, sur **ton** ℕ, avec tes lemmes (sans `grind`).

## À prouver
`somme_impairs (n : ℕ) : impairs n = n * n`""",
 """/-- `impairs n = 1 + 3 + ⋯ + (2n - 1)` -/
def impairs : ℕ → ℕ
  | zero => 0
  | succ n => impairs n + (2 * n + 1)

theorem somme_impairs (n : ℕ) : impairs n = n * n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    show impairs n + (2 * n + 1) = succ n * succ n
    rw [ih, mul_succ, succ_mul, two_mul, add_assoc (n * n) n (succ n), add_succ]
    rfl""",
 ["Récurrence. `impairs (succ n) = impairs n + (2n + 1)` par définition (`show`).", "À droite : `succ n * succ n = n * n + n + succ n` (`mul_succ`, `succ_mul`). À gauche : `two_mul`. Puis réarrange avec `add_assoc` et `add_succ` : il reste une égalité vraie par définition."], NSN, requiert="Naturels.SuccMul")

NSL = "Parcours.Listes.Liste"
exo("Listes", "Palindromes", "Les palindromes", 2, ["Solutions.Listes.Miroir"],
 """Un **palindrome** se lit pareil dans les deux sens (« ressasser », `[1, 2, 1]`).
Coller une liste et son miroir donne toujours un palindrome.

## À prouver
`palindrome (l : Liste α) : miroir (l ++ miroir l) = l ++ miroir l`""",
 """theorem palindrome {α : Type} (l : Liste α) : miroir (l ++ miroir l) = l ++ miroir l := by -- @exo
  rw [miroir_concat, miroir_miroir]""",
 ["Deux réécritures suffisent : `miroir_concat` puis `miroir_miroir`."], NSL, requiert="Listes.Miroir")
exo("Listes", "Aplatir", "Aplatir une liste de listes", 3, ["Solutions.Listes.Plis", "Solutions.Listes.Longueur"],
 """`aplatir [[1, 2], [], [3]] = [1, 2, 3]`. Sa longueur est la somme des longueurs.

## À prouver
`longueur_aplatir : longueur (aplatir ll) = somme (map longueur ll)`""",
 """def aplatir {α : Type} : Liste (Liste α) → Liste α
  | nil => nil
  | l ∷ ll => l ++ aplatir ll

theorem longueur_aplatir {α : Type} (ll : Liste (Liste α)) :
    longueur (aplatir ll) = somme (map longueur ll) := by -- @exo
  induction ll with
  | nil => rfl
  | cons l ll ih =>
    show longueur (l ++ aplatir ll) = longueur l + somme (map longueur ll)
    rw [longueur_concat, ih]""",
 ["Récurrence sur `ll` ; dans le cas `cons`, `show` déplie les définitions.", "`longueur_concat` puis l'hypothèse de récurrence."], NSL, requiert="Listes.Plis")
exo("Listes", "Zip", "Fermeture éclair (zip)", 3, ["Solutions.Listes.Longueur"],
 """`zip [1, 2, 3] [a, b] = [(1, a), (2, b)]` : on assemble deux listes deux à deux, en s'arrêtant à la plus courte.

## À prouver
`longueur_zip : longueur (zip l₁ l₂) = min (longueur l₁) (longueur l₂)`""",
 """def zip {α β : Type} : Liste α → Liste β → Liste (α × β)
  | x ∷ l₁, y ∷ l₂ => (x, y) ∷ zip l₁ l₂
  | _, _ => nil

theorem longueur_zip {α β : Type} (l₁ : Liste α) (l₂ : Liste β) :
    longueur (zip l₁ l₂) = min (longueur l₁) (longueur l₂) := by -- @exo
  induction l₁ generalizing l₂ with
  | nil => simp [zip, longueur]
  | cons x l₁ ih =>
    cases l₂ with
    | nil => simp [zip, longueur]
    | cons y l₂ =>
      show longueur (zip l₁ l₂) + 1 = min (longueur l₁ + 1) (longueur l₂ + 1)
      rw [ih]
      omega""",
 ["Récurrence sur `l₁` en généralisant `l₂`, puis `cases l₂`.", "Les cas avec une liste vide : `simp [zip, longueur]`. Le cas récursif : `show`, `ih`, puis `omega` (qui connaît `min`)."], NSL, requiert="Listes.PrendreJeter")

NSG = "Parcours.Logique"
exo("Logique", "TablesVerite", "Tables de vérité", 1, ["ParcoursOutils"],
 """En Lean il y a deux mondes : les **propositions** (`Prop`, ce qu'on prouve) et les **booléens**
(`Bool`, ce qu'on calcule). `&&`, `||`, `!` sont les versions calculables de `∧`, `∨`, `¬`.
Comme un booléen n'a que deux valeurs, une égalité de booléens se vérifie en essayant tous les cas :
c'est la méthode des **tables de vérité**.

## À prouver
1. `de_morgan_bool : !(a && b) = (!a || !b)`
2. `distrib_bool : (a && (b || c)) = ((a && b) || (a && c))`
3. `et_vrai_iff : (a && b) = true ↔ a = true ∧ b = true`""",
 """theorem de_morgan_bool (a b : Bool) : (!(a && b)) = (!a || !b) := by -- @exo
  cases a <;> cases b <;> rfl

theorem distrib_bool (a b c : Bool) : (a && (b || c)) = ((a && b) || (a && c)) := by -- @exo
  cases a <;> cases b <;> cases c <;> rfl

theorem et_vrai_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by -- @exo
  revert a b
  decide""",
 ["`cases a <;> cases b <;> rfl` essaie toutes les valeurs.", "Pour une équivalence : `revert a b` puis `decide`."], NSG, requiert="Logique.Et")
exo("Logique", "Circulaire", "Implications circulaires", 2, ["ParcoursOutils"],
 """Pour montrer que trois propositions sont équivalentes, il suffit d'un **cycle** d'implications :
`P → Q → R → P`. Technique très utilisée dans les livres de maths (« les assertions suivantes sont équivalentes »).

## À prouver
`circulaire : (P → Q) → (Q → R) → (R → P) → (P ↔ Q) ∧ (Q ↔ R)`""",
 """theorem circulaire {P Q R : Prop} (h1 : P → Q) (h2 : Q → R) (h3 : R → P) :
    (P ↔ Q) ∧ (Q ↔ R) := by -- @exo
  exact ⟨⟨h1, fun q => h3 (h2 q)⟩, ⟨h2, fun r => h1 (h3 r)⟩⟩""",
 ["Chaque sens d'équivalence s'obtient en composant les implications.", "`exact ⟨⟨h1, fun q => h3 (h2 q)⟩, ⟨h2, fun r => …⟩⟩`."], NSG, requiert="Logique.Equivalence")
exo("Logique", "OuExclusif", "Le ou exclusif", 2, ["ParcoursOutils"],
 """« Ou bien P, ou bien Q, mais pas les deux » : le **ou exclusif** (XOR).

## À prouver
1. `oux_comm : OuX P Q → OuX Q P`
2. `oux_soi : ¬OuX P P`
3. `oux_faux : OuX P False ↔ P`""",
 """def OuX (P Q : Prop) : Prop := (P ∨ Q) ∧ ¬(P ∧ Q)

theorem oux_comm {P Q : Prop} (h : OuX P Q) : OuX Q P := by -- @exo
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1.elim Or.inr Or.inl, fun ⟨hq, hp⟩ => h2 ⟨hp, hq⟩⟩

theorem oux_soi (P : Prop) : ¬OuX P P := by -- @exo
  rintro ⟨h1, h2⟩
  rcases h1 with hp | hp <;> exact h2 ⟨hp, hp⟩

theorem oux_faux (P : Prop) : OuX P False ↔ P := by -- @exo
  constructor
  · rintro ⟨h | h, _⟩
    · exact h
    · exact h.elim
  · intro hp
    exact ⟨Or.inl hp, fun ⟨_, f⟩ => f⟩""",
 ["Déplie la définition avec `obtain ⟨h1, h2⟩ := h` ou `rintro ⟨h1, h2⟩`.", "`h.elim Or.inr Or.inl` transforme `P ∨ Q` en `Q ∨ P`."], NSG, requiert="Logique.Negation")
exo("Logique", "PasDePlusPetit", "Pas de plus petit que zéro", 2, ["ParcoursOutils"],
 """Contre-exemple à « pour tout `n`, il existe `m < n` » : prends `n = 0` ! En Lean, `m < 0` est
impossible, et `cases` le voit (aucune règle ne permet de construire une preuve de `m < 0`).

## À prouver
`pas_de_plus_petit : ¬∀ n : Nat, ∃ m, m < n`""",
 """theorem pas_de_plus_petit : ¬∀ n : Nat, ∃ m, m < n := by -- @exo
  intro h
  obtain ⟨m, hm⟩ := h 0
  cases hm""",
 ["`intro h`, puis applique `h` à `0`.", "Avec `hm : m < 0`, `cases hm` termine (il n'y a aucun cas possible)."], NSG, requiert="Logique.NegQuantif")

NSF = "Parcours.Fonctions"
exo("Fonctions", "Involutions", "Les involutions", 2, ["Solutions.Fonctions.Inverses"],
 """Une **involution** est une fonction qui est sa propre réciproque : `f (f x) = x` (comme la négation,
le passage à l'opposé, ou le miroir d'une liste). Une involution est toujours bijective.

## À prouver
`involution_bijective (h : ∀ x, f (f x) = x) : Bijective f`""",
 """theorem involution_bijective {α : Type} {f : α → α} (h : ∀ x, f (f x) = x) : Bijective f := by -- @exo
  exact ⟨injective_of_inverse_gauche h, surjective_of_inverse_droite h⟩""",
 ["`f` est son propre inverse à gauche ET à droite : tu as déjà les deux théorèmes qu'il faut (exercice « Inverses »)."], NSF, requiert="Fonctions.Inverses")
exo("Fonctions", "ImageComposee", "Image par une composée", 2, ["Solutions.Fonctions.Definitions"],
 """L'image d'un ensemble par `g ∘ f` est l'image par `g` de l'image par `f`.

## À prouver
`image_comp : (g ∘ f) '' s = g '' (f '' s)`""",
 """theorem image_comp {α β γ : Type} (f : α → β) (g : β → γ) (s : Ens α) :
    (g ∘ f) '' s = g '' (f '' s) := by -- @exo
  apply ext
  intro z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩""",
 ["`apply ext`, puis deux sens. Utilise `rintro ⟨x, hx, rfl⟩` pour déstructurer une appartenance à une image."], NSF, requiert="Fonctions.Images")

ecrire_tout()
