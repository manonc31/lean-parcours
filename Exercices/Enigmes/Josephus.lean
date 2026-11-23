import Exercices.Recurrence.Definitions

/-!
# Le problème de Josèphe

`n` personnes en cercle, numérotées de 1 à `n`. On élimine **une personne sur deux** (la 2, la 4, …)
en tournant, jusqu'à ce qu'il n'en reste qu'une. Qui survit ? (L'historien Flavius Josèphe aurait
utilisé ce calcul pour survivre, en l'an 67.)

En analysant un tour de cercle, on trouve la récurrence :
`J(1) = 1`, `J(2k) = 2 J(k) − 1`, `J(2k + 1) = 2 J(k) + 1`.

Et une formule magique : si `n = 2ᵐ + l` avec `l < 2ᵐ`, alors `J(n) = 2l + 1`.
(En binaire : on fait tourner le premier chiffre de `n` à la fin !)

## À prouver
`josephe_formule (m l : Nat) (hl : l < 2 ^ m) : josephe (2 ^ m + l) = 2 * l + 1`

## Ressources
- [Problème de Josèphe (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_de_Jos%C3%A8phe)

---
*Exercice* `Enigmes.Josephus` · difficulté ★★★★☆

💡 Indices : `./parcours indice Enigmes.Josephus` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Enigmes

def josephe (n : Nat) : Nat :=
  if n ≤ 1 then 1
  else if n % 2 = 0 then 2 * josephe (n / 2) - 1
  else 2 * josephe (n / 2) + 1
termination_by n
decreasing_by all_goals omega

theorem josephe_formule (m l : Nat) (hl : l < 2 ^ m) : josephe (2 ^ m + l) = 2 * l + 1 := by
  sorry

end Parcours.Enigmes

#verifier
