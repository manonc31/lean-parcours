import Exercices.Listes.Pont
import Exercices.Recurrence.Definitions

/-!
# Le code correcteur de Hamming

Comment une sonde spatiale ou une barrette de mémoire corrige-t-elle les erreurs de transmission ?
Le **code de Hamming** (1950) ajoute 3 bits de contrôle à 4 bits de données. Si **un** bit (n'importe
lequel des 7) est inversé pendant le transport, le récepteur le repère et le corrige : le
« syndrome » (3 bits de parité recalculés) donne directement la position de l'erreur !

## À prouver
1. `corrige_une_erreur` : pour les 16 messages et les 8 situations (aucune erreur ou une erreur à
   l'une des 7 positions), on retrouve le message.
2. `deux_erreurs` : avec deux erreurs, le code peut se tromper.

## Ressources
- [Code de Hamming (Wikipédia)](https://fr.wikipedia.org/wiki/Code_de_Hamming)

---
*Exercice* `Informatique.Hamming` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Informatique.Hamming` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Info

def encoderH (d : List Bool) : List Bool :=
  let d1 := d.getD 0 false
  let d2 := d.getD 1 false
  let d3 := d.getD 2 false
  let d4 := d.getD 3 false
  [d1 ^^ d2 ^^ d4, d1 ^^ d3 ^^ d4, d1, d2 ^^ d3 ^^ d4, d2, d3, d4]

/-- La position de l'erreur (de 1 à 7), ou 0 s'il n'y en a pas. -/
def syndrome (c : List Bool) : Nat :=
  let b := fun i => c.getD (i - 1) false
  (b 1 ^^ b 3 ^^ b 5 ^^ b 7).toNat + 2 * (b 2 ^^ b 3 ^^ b 6 ^^ b 7).toNat +
    4 * (b 4 ^^ b 5 ^^ b 6 ^^ b 7).toNat

/-- Inverse le bit en position `i` (de 1 à 7) ; `i = 0` : ne fait rien. -/
def inverser (c : List Bool) (i : Nat) : List Bool :=
  if i = 0 then c else c.set (i - 1) (!(c.getD (i - 1) false))

def decoderH (c : List Bool) : List Bool :=
  let c' := inverser c (syndrome c)
  [c'.getD 2 false, c'.getD 4 false, c'.getD 5 false, c'.getD 6 false]

def messages : List (List Bool) :=
  [false, true].flatMap fun a => [false, true].flatMap fun b => [false, true].flatMap fun c =>
    [false, true].map fun d => [a, b, c, d]

theorem corrige_une_erreur : ∀ d ∈ messages, ∀ i, i < 8 → decoderH (inverser (encoderH d) i) = d := by
  sorry

theorem deux_erreurs : ∃ d ∈ messages, decoderH (inverser (inverser (encoderH d) 1) 2) ≠ d := by
  sorry

end Parcours.Info

#verifier
