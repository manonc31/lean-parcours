/- @parcours
titre: Espérance et inégalité de Markov
difficulte: 3
indice: `linearite` : récurrence sur `Ω` ; `List.map_cons`, `List.sum_cons`, puis `omega`.
indice: `markov` : récurrence sur `Ω`. Pour `ω :: Ω`, raisonne par cas sur `a ≤ X ω` : `by_cases h : a ≤ X ω`, puis `simp [List.countP_cons, h]` et `Nat.add_mul`, puis `omega`.
indice: `esperance_de` : c'est un calcul (`decide`).
-/
import Solutions.Probabilites.Definitions

/-!
# Espérance et inégalité de Markov

L'**espérance** d'une quantité aléatoire `X` est sa moyenne : `E[X] = (Σ X(ω)) / |Ω|`. On manipule
ici la somme `Σ X(ω)` (pour éviter les divisions).

- **Linéarité** : `E[X + Y] = E[X] + E[Y]`, même si `X` et `Y` ne sont pas indépendantes !
- **Inégalité de Markov** : si `X ≥ 0`, alors `P(X ≥ a) ≤ E[X] / a`. Sous forme de somme :
  `(nombre de ω avec X ω ≥ a) × a ≤ Σ X(ω)`.

## À prouver
1. `esperance_de` : la moyenne d'un dé est 7/2 (`2 × (1+2+⋯+6) = 7 × 6`).
2. `linearite : (Ω.map (fun ω => X ω + Y ω)).sum = (Ω.map X).sum + (Ω.map Y).sum`
3. `markov : Ω.countP (fun ω => decide (a ≤ X ω)) * a ≤ (Ω.map X).sum`

## Ressources
- [Espérance mathématique (Wikipédia)](https://fr.wikipedia.org/wiki/Esp%C3%A9rance_math%C3%A9matique)
- [Inégalité de Markov (Wikipédia)](https://fr.wikipedia.org/wiki/In%C3%A9galit%C3%A9_de_Markov)
-/

namespace Parcours.Proba

theorem esperance_de : 2 * (de.map id).sum = 7 * de.length := by -- @exo
  decide

theorem linearite {α : Type} (Ω : List α) (X Y : α → Nat) :
    (Ω.map (fun ω => X ω + Y ω)).sum = (Ω.map X).sum + (Ω.map Y).sum := by -- @exo
  induction Ω with
  | nil => rfl
  | cons ω Ω ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem markov {α : Type} (Ω : List α) (X : α → Nat) (a : Nat) :
    Ω.countP (fun ω => decide (a ≤ X ω)) * a ≤ (Ω.map X).sum := by -- @exo
  induction Ω with
  | nil => simp
  | cons ω Ω ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons]
    by_cases h : a ≤ X ω
    · simp only [h, decide_true, if_true, Nat.add_mul, Nat.one_mul]
      omega
    · simp only [h, decide_false]
      simp
      omega

end Parcours.Proba

#verifier
