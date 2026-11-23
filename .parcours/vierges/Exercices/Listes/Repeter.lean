import Exercices.Listes.Longueur

/-!
# Répéter et compter

- `repeter n x` : la liste `[x, x, …, x]` (`n` fois).
- `compter x l` : le nombre d'occurrences de `x` dans `l`.

## À prouver
1. `longueur_repeter : longueur (repeter n x) = n`
2. `compter_repeter : compter x (repeter n x) = n`
3. `compter_concat : compter x (l₁ ++ l₂) = compter x l₁ + compter x l₂`

---
*Exercice* `Listes.Repeter` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Listes.Repeter` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Listes.Liste

def repeter {α : Type} : Nat → α → Liste α
  | 0, _ => nil
  | n + 1, x => x ∷ repeter n x

def compter (x : Nat) : Liste Nat → Nat
  | nil => 0
  | y ∷ l => (if y = x then 1 else 0) + compter x l

theorem longueur_repeter {α : Type} (n : Nat) (x : α) : longueur (repeter n x) = n := by
  sorry

theorem compter_repeter (n x : Nat) : compter x (repeter n x) = n := by
  sorry

theorem compter_concat (x : Nat) (l₁ l₂ : Liste Nat) :
    compter x (l₁ ++ l₂) = compter x l₁ + compter x l₂ := by
  sorry

end Parcours.Listes.Liste

#verifier
