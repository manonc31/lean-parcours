import Exercices.Informatique.Expressions

/-!
# Le langage IMP

Un petit langage impératif : affectation `x := a`, séquence `c₁ ; c₂`, `si b alors c₁ sinon c₂`,
`tant que b faire c`. Un **état** (`Store`) donne la valeur de chaque variable.

La **sémantique** est une relation inductive `Exec c s s'` : « exécuter `c` dans l'état `s` termine
dans l'état `s'` ». (Une relation et pas une fonction, car un programme peut ne pas terminer !)
Les expressions `a` et `b` sont directement des fonctions de l'état (pour simplifier).

## À prouver
1. `determinisme : Exec c s s₁ → Exec c s s₂ → s₁ = s₂`
2. `boucle_infinie : ¬Exec (tantque (fun _ => true) skip) s s'`

## Ressources
- [Sémantique opérationnelle (Wikipédia)](https://fr.wikipedia.org/wiki/S%C3%A9mantique_op%C3%A9rationnelle)
- [Software Foundations, volume 1, chapitre Imp](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html) (en Coq, le cousin de Lean)

---
*Exercice* `Informatique.IMP` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Informatique.IMP` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Info

abbrev Store := Nat → Nat

def maj (s : Store) (x v : Nat) : Store := fun y => if y = x then v else s y

inductive Com where
  | skip
  | assign (x : Nat) (a : Store → Nat)
  | seq (c₁ c₂ : Com)
  | si (b : Store → Bool) (c₁ c₂ : Com)
  | tantque (b : Store → Bool) (c : Com)

open Com

inductive Exec : Com → Store → Store → Prop
  | skip (s : Store) : Exec skip s s
  | assign (s : Store) (x : Nat) (a : Store → Nat) : Exec (assign x a) s (maj s x (a s))
  | seq {c₁ c₂ : Com} {s s' s'' : Store} : Exec c₁ s s' → Exec c₂ s' s'' → Exec (seq c₁ c₂) s s''
  | si_vrai {b : Store → Bool} {c₁ c₂ : Com} {s s' : Store} :
      b s = true → Exec c₁ s s' → Exec (si b c₁ c₂) s s'
  | si_faux {b : Store → Bool} {c₁ c₂ : Com} {s s' : Store} :
      b s = false → Exec c₂ s s' → Exec (si b c₁ c₂) s s'
  | tq_faux {b : Store → Bool} {c : Com} {s : Store} : b s = false → Exec (tantque b c) s s
  | tq_vrai {b : Store → Bool} {c : Com} {s s' s'' : Store} :
      b s = true → Exec c s s' → Exec (tantque b c) s' s'' → Exec (tantque b c) s s''

theorem determinisme {c : Com} {s s₁ s₂ : Store} (h₁ : Exec c s s₁) (h₂ : Exec c s s₂) : s₁ = s₂ := by
  sorry

theorem boucle_infinie (s s' : Store) : ¬Exec (tantque (fun _ => true) skip) s s' := by
  sorry

end Parcours.Info

#verifier
