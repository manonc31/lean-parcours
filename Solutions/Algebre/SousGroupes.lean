/- @parcours
titre: Sous-groupes
difficulte: 2
indice: Pour construire un sous-groupe, donne les 4 champs : `refine ⟨fun x => …, ?_, ?_, ?_⟩`.
indice: Intersection : chaque propriété découle des propriétés de `H` et de `K` (`⟨H.one_mem, K.one_mem⟩`…).
indice: Centre : pour `mul_mem`, `(a * b) * g = a * (b * g) = a * (g * b) = (a * g) * b = …`. Pour `inv_mem`, multiplie `a * g = g * a` à gauche et à droite par `a⁻¹`.
-/
import Solutions.Algebre.Inverses

/-!
# Sous-groupes

Un **sous-groupe** de `G` est une partie qui contient `1`, et qui est stable par `*` et `⁻¹`.

## À faire
1. `inter H K` : l'intersection de deux sous-groupes est un sous-groupe.
2. `centre G` : les éléments qui commutent avec tout le monde forment un sous-groupe.
-/

namespace Parcours.Algebre

variable {G : Type} [Groupe G]

structure SousGroupe (G : Type) [Groupe G] where
  mem : G → Prop
  one_mem : mem 1
  mul_mem : ∀ {a b}, mem a → mem b → mem (a * b)
  inv_mem : ∀ {a}, mem a → mem a⁻¹

def SousGroupe.inter (H K : SousGroupe G) : SousGroupe G := by -- @exo
  refine ⟨fun x => H.mem x ∧ K.mem x, ⟨H.one_mem, K.one_mem⟩, ?_, ?_⟩
  · intro a b ha hb
    exact ⟨H.mul_mem ha.1 hb.1, K.mul_mem ha.2 hb.2⟩
  · intro a ha
    exact ⟨H.inv_mem ha.1, K.inv_mem ha.2⟩

def centre (G : Type) [Groupe G] : SousGroupe G := by -- @exo
  refine ⟨fun a => ∀ g : G, a * g = g * a, ?_, ?_, ?_⟩
  · intro g
    rw [Groupe.one_mul, mul_one]
  · intro a b ha hb g
    rw [Groupe.mul_assoc, hb g, ← Groupe.mul_assoc, ha g, Groupe.mul_assoc]
  · intro a ha g
    calc a⁻¹ * g = a⁻¹ * (g * a) * a⁻¹ := by rw [Groupe.mul_assoc, Groupe.mul_assoc g a a⁻¹, mul_inv, mul_one]
      _ = a⁻¹ * (a * g) * a⁻¹ := by rw [ha g]
      _ = g * a⁻¹ := by rw [← Groupe.mul_assoc, Groupe.inv_mul, Groupe.one_mul]

end Parcours.Algebre

#verifier
