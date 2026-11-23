import Exercices.Informatique.IMP

/-!
# La logique de Hoare

Un **triplet de Hoare** `{P} c {Q}` signifie : si `P` est vraie avant d'exécuter `c`, et si `c`
termine, alors `Q` est vraie après. C'est **la** méthode pour prouver des programmes (Hoare, 1969).

La règle la plus importante, celle des boucles, utilise un **invariant** `I` :
si `{I ∧ b} c {I}`, alors `{I} tantque b faire c {I ∧ ¬b}`.

## À prouver (correction des règles)
1. `hoare_skip : {P} skip {P}`
2. `hoare_seq : {P} c₁ {Q} → {Q} c₂ {R} → {P} c₁; c₂ {R}`
3. `hoare_si : {P ∧ b} c₁ {Q} → {P ∧ ¬b} c₂ {Q} → {P} si b alors c₁ sinon c₂ {Q}`
4. `hoare_tantque : {I ∧ b} c {I} → {I} tantque b faire c {I ∧ ¬b}`

## Ressources
- [Logique de Hoare (Wikipédia)](https://fr.wikipedia.org/wiki/Logique_de_Hoare)

---
*Exercice* `Informatique.Hoare` · difficulté ★★★★☆

💡 Indices : `./parcours indice Informatique.Hoare` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Info

open Com

/-- Le triplet de Hoare `{P} c {Q}`. -/
def Hoare (P : Store → Prop) (c : Com) (Q : Store → Prop) : Prop :=
  ∀ s s', P s → Exec c s s' → Q s'

theorem hoare_skip (P : Store → Prop) : Hoare P skip P := by
  sorry

theorem hoare_seq {P Q R : Store → Prop} {c₁ c₂ : Com} (h₁ : Hoare P c₁ Q) (h₂ : Hoare Q c₂ R) :
    Hoare P (seq c₁ c₂) R := by
  sorry

theorem hoare_si {P Q : Store → Prop} {b : Store → Bool} {c₁ c₂ : Com}
    (h₁ : Hoare (fun s => P s ∧ b s = true) c₁ Q) (h₂ : Hoare (fun s => P s ∧ b s = false) c₂ Q) :
    Hoare P (si b c₁ c₂) Q := by
  sorry

theorem hoare_tantque {I : Store → Prop} {b : Store → Bool} {c : Com}
    (h : Hoare (fun s => I s ∧ b s = true) c I) :
    Hoare I (tantque b c) (fun s => I s ∧ b s = false) := by
  sorry

end Parcours.Info

#verifier
