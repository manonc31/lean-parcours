/- @parcours
titre: Le noyau d'un morphisme
difficulte: 3
indice: Le noyau est un sous-groupe : `map_one`, `map_mul`, `map_inv`.
indice: Injectivité, sens `←` : si `f a = f b`, alors `f (a * b⁻¹) = f a * (f b)⁻¹ = 1`, donc `a * b⁻¹ = 1`, donc `a = b` (multiplie à droite par `b`).
-/
import Solutions.Algebre.Morphismes
import Solutions.Algebre.SousGroupes

/-!
# Le noyau d'un morphisme

Le **noyau** de `f` : les `a` tels que `f a = 1`. C'est un sous-groupe, et il mesure exactement
le défaut d'injectivité : `f` est injectif si et seulement si son noyau est `{1}`.

## À faire
1. `Morphisme.noyau : SousGroupe G`
2. `injectif_iff_noyau : (∀ a b, f a = f b → a = b) ↔ (∀ a, f a = 1 → a = 1)`
-/

namespace Parcours.Algebre

variable {G H : Type} [Groupe G] [Groupe H]

def Morphisme.noyau (φ : Morphisme G H) : SousGroupe G := by -- @exo
  refine ⟨fun a => φ.f a = 1, φ.map_one, ?_, ?_⟩
  · intro a b ha hb
    show φ.f (a * b) = 1
    rw [φ.map_mul, ha, hb, Groupe.one_mul]
  · intro a ha
    show φ.f a⁻¹ = 1
    rw [φ.map_inv, ha, inv_one]

theorem injectif_iff_noyau (φ : Morphisme G H) :
    (∀ a b, φ.f a = φ.f b → a = b) ↔ (∀ a, φ.f a = 1 → a = 1) := by -- @exo
  constructor
  · intro hinj a ha
    exact hinj a 1 (by rw [ha, φ.map_one])
  · intro hker a b hab
    have h1 : a * b⁻¹ = 1 := hker _ (by rw [φ.map_mul, φ.map_inv, hab, mul_inv])
    calc a = a * b⁻¹ * b := by rw [Groupe.mul_assoc, Groupe.inv_mul, mul_one]
      _ = b := by rw [h1, Groupe.one_mul]

end Parcours.Algebre

#verifier
