/- @parcours
titre: Les matrices 2×2
difficulte: 1
genre: cours
requiert: Algebre.Inverses
-/
import Solutions.Recurrence.Definitions

/-!
# Les matrices 2×2 (cours)

Une matrice `2×2` à coefficients entiers :
```
⎛ a  b ⎞
⎝ c  d ⎠
```
Le produit se fait « ligne × colonne », et le **déterminant** vaut `ad − bc`.
Les matrices sont partout : géométrie (rotations), graphismes, graphes, physique, et même… Fibonacci.

## Outils
- `M2.ext` : deux matrices sont égales si leurs 4 coefficients le sont.
- `M2.mul_def` : la formule du produit.
- Méthode type : `obtain ⟨a, b, c, d⟩ := A` (idem pour `B`…), puis `simp only [M2.mul_def, M2.mk.injEq]`,
  puis `refine ⟨?_, ?_, ?_, ?_⟩ <;> grind`.

## Ressources
- [Matrice (Wikipédia)](https://fr.wikipedia.org/wiki/Matrice_(math%C3%A9matiques))
-/

namespace Parcours.Matrices

/-- Une matrice 2×2 à coefficients entiers. -/
structure M2 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq, Repr

namespace M2

def mul (A B : M2) : M2 :=
  ⟨A.a * B.a + A.b * B.c, A.a * B.b + A.b * B.d, A.c * B.a + A.d * B.c, A.c * B.b + A.d * B.d⟩

instance : Mul M2 := ⟨mul⟩

def id2 : M2 := ⟨1, 0, 0, 1⟩

def det (A : M2) : Int := A.a * A.d - A.b * A.c

theorem mul_def (A B : M2) : A * B =
    ⟨A.a * B.a + A.b * B.c, A.a * B.b + A.b * B.d, A.c * B.a + A.d * B.c, A.c * B.b + A.d * B.d⟩ := rfl

theorem ext {A B : M2} (ha : A.a = B.a) (hb : A.b = B.b) (hc : A.c = B.c) (hd : A.d = B.d) : A = B := by
  cases A; cases B; simp_all

/-- Puissance d'une matrice. -/
def puiss (A : M2) : Nat → M2
  | 0 => id2
  | n + 1 => puiss A n * A

end M2
end Parcours.Matrices
