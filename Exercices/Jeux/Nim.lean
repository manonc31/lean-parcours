import Exercices.Recurrence.Definitions

/-!
# Le jeu de Nim à un tas

Il y a `n` allumettes. Chacun son tour, un joueur en retire 1, 2 ou 3. Celui qui prend la
**dernière** gagne. (Version popularisée par l'émission Fort Boyard !)

Une position est **gagnante** si le joueur dont c'est le tour peut forcer la victoire :
c'est le cas s'il existe un coup qui mène à une position **perdante** pour l'adversaire.

**Théorème** : les positions perdantes sont exactement les multiples de 4.
Stratégie : laisse toujours un multiple de 4 à ton adversaire !

## À prouver
`nim (n : Nat) : gagnante n = (n % 4 != 0)`

## Ressources
- [Jeu de Nim (Wikipédia)](https://fr.wikipedia.org/wiki/Jeux_de_Nim)

---
*Exercice* `Jeux.Nim` · difficulté ★★★☆☆

💡 Indices : `./parcours indice Jeux.Nim` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Jeux

/-- `gagnante n` : avec `n` allumettes, le joueur qui doit jouer peut-il forcer la victoire ? -/
def gagnante : Nat → Bool
  | 0 => false
  | 1 => true
  | 2 => true
  | n + 3 => !gagnante (n + 2) || !gagnante (n + 1) || !gagnante n

theorem nim (n : Nat) : gagnante n = (n % 4 != 0) := by
  sorry

end Parcours.Jeux

#verifier
