import Exercices.Circuits.Definitions

/-!
# Le soustracteur complet

Pour soustraire en binaire, on procède comme à l'école, avec une **retenue** (un « emprunt ») :
`a − b − emprunt`. Le résultat est un bit de différence et un nouvel emprunt.

## À prouver
`soustracteur_ok : a + 2 × emprunt_sortant = b + emprunt_entrant + différence` (en valeurs
`0`/`1`).

---
*Exercice* `Circuits.Soustracteur` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Circuits.Soustracteur` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Circuits

def difference (a b e : Bool) : Bool := xor (xor a b) e
def emprunt (a b e : Bool) : Bool := (!a && b) || (!(xor a b) && e)

theorem soustracteur_ok (a b e : Bool) :
    a.toNat + 2 * (emprunt a b e).toNat = b.toNat + e.toNat + (difference a b e).toNat := by
  sorry

end Parcours.Circuits

#verifier
