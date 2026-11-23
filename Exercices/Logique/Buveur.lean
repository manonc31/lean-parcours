import Exercices.Logique.NegQuantif

/-!
# Le paradoxe du buveur

> Dans tout bar non vide, il y a quelqu'un tel que, **s'il boit, alors tout le monde boit**.

Ça a l'air absurde, et pourtant c'est un théorème (de logique classique). Le piège est dans
le sens du mot « si… alors ». Popularisé par Raymond Smullyan.

`[Nonempty α]` signifie que le bar contient au moins une personne.

## À prouver
`buveur : ∃ x, boit x → ∀ y, boit y`

## Ressources
- [Paradoxe du buveur (Wikipédia)](https://fr.wikipedia.org/wiki/Paradoxe_du_buveur)

---
*Exercice* `Logique.Buveur` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Logique.Buveur` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

theorem buveur {α : Type} [Nonempty α] (boit : α → Prop) : ∃ x, boit x → ∀ y, boit y := by
  sorry

end Parcours.Logique

#verifier
