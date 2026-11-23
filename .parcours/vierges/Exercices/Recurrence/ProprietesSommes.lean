import Exercices.Recurrence.Definitions

/-!
# Manipuler des sommes

Les règles de calcul sur `Σ` qu'on utilise sans y penser : linéarité, décalage d'indice,
termes égaux ⇒ sommes égales. Elles serviront pour le binôme de Newton.

## À prouver
1. `somme_add : somme (fun k => f k + g k) n = somme f n + somme g n`
2. `somme_mul : somme (fun k => c * f k) n = c * somme f n`
3. `somme_decale : somme f (n + 1) = f 0 + somme (fun k => f (k + 1)) n`
4. `somme_congr : (∀ k, k < n → f k = g k) → somme f n = somme g n`
5. `divise_somme : (∀ k, k < n → d ∣ f k) → d ∣ somme f n`

---
*Exercice* `Recurrence.ProprietesSommes` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Recurrence.ProprietesSommes` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Recurrence

theorem somme_add (f g : Nat → Nat) (n : Nat) :
    somme (fun k => f k + g k) n = somme f n + somme g n := by
  sorry

theorem somme_mul (c : Nat) (f : Nat → Nat) (n : Nat) :
    somme (fun k => c * f k) n = c * somme f n := by
  sorry

theorem somme_decale (f : Nat → Nat) (n : Nat) :
    somme f (n + 1) = f 0 + somme (fun k => f (k + 1)) n := by
  sorry

theorem somme_congr {f g : Nat → Nat} {n : Nat} (h : ∀ k, k < n → f k = g k) :
    somme f n = somme g n := by
  sorry

theorem divise_somme {d : Nat} {f : Nat → Nat} {n : Nat} (h : ∀ k, k < n → d ∣ f k) :
    d ∣ somme f n := by
  sorry

end Parcours.Recurrence

#verifier
