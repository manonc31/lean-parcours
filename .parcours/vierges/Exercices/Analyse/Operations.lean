import Exercices.Analyse.ValeurAbsolue

/-!
# Somme de limites et théorème des gendarmes

## À prouver
1. `somme_limites : Tend u a → Tend v b → Tend (fun n => u n + v n) (a + b)`
2. `gendarmes` : si `u n ≤ v n ≤ w n` et si `u` et `w` tendent vers `l`, alors `v` aussi.

## Ressources
- [Théorème des gendarmes (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_des_gendarmes)

---
*Exercice* `Analyse.Operations` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Analyse.Operations` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Analyse

theorem somme_limites {u v : Suite} {a b : Rat} (hu : Tend u a) (hv : Tend v b) :
    Tend (fun n => u n + v n) (a + b) := by
  sorry

theorem gendarmes {u v w : Suite} {l : Rat} (hu : Tend u l) (hw : Tend w l)
    (h1 : ∀ n, u n ≤ v n) (h2 : ∀ n, v n ≤ w n) : Tend v l := by
  sorry

end Parcours.Analyse

#verifier
