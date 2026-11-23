/- @parcours
titre: Le paradoxe du buveur
difficulte: 3
indice: Raisonne par cas : soit tout le monde boit, soit non (`Classical.em (∀ y, boit y)`).
indice: Si tout le monde boit, n'importe qui convient. Pour obtenir quelqu'un, `obtain ⟨a⟩ := ‹Nonempty α›` (le type n'est pas vide).
indice: Sinon, `non_pourtout` donne un `x` qui ne boit pas. Pour lui, « s'il boit alors… » est vrai, car il ne boit pas !
-/
import Solutions.Logique.NegQuantif

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
-/

namespace Parcours.Logique

theorem buveur {α : Type} [Nonempty α] (boit : α → Prop) : ∃ x, boit x → ∀ y, boit y := by -- @exo
  rcases Classical.em (∀ y, boit y) with h | h
  · obtain ⟨a⟩ := ‹Nonempty α›
    exact ⟨a, fun _ => h⟩
  · obtain ⟨x, hx⟩ := non_pourtout.mp h
    exact ⟨x, fun hb => absurd hb hx⟩

end Parcours.Logique

#verifier
