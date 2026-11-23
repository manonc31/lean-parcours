/- @parcours
titre: Chemins dans une grille
difficulte: 3
requiert: Combinatoire.BinomBase
indice: Double récurrence : sur `m` (en généralisant `n`), puis sur `n`.
indice: Cas récursif : déplie avec `simp only [chemins]`, applique les deux hypothèses de récurrence, puis la formule de Pascal `binom_succ_succ`. Ajuste les sommes d'indices avec `show … by omega`.
-/
import Solutions.Combinatoire.BinomBase

/-!
# Chemins dans une grille

Combien de chemins pour aller du coin `(0, 0)` au coin `(m, n)` d'une grille, en ne faisant que des pas
vers la droite ou vers le haut ? `chemins m n` les compte récursivement (le dernier pas vient de la gauche
ou d'en bas). La réponse : `C(m + n, m)`, on choisit les positions des `m` pas vers la droite.

## À prouver
`chemins_binom (m n : Nat) : chemins m n = binom (m + n) m`
-/

namespace Parcours.Combi

def chemins : Nat → Nat → Nat
  | 0, _ => 1
  | _, 0 => 1
  | m + 1, n + 1 => chemins m (n + 1) + chemins (m + 1) n

theorem chemins_binom (m n : Nat) : chemins m n = binom (m + n) m := by -- @exo
  induction m generalizing n with
  | zero => simp [chemins, binom_zero_droite]
  | succ m ih =>
    induction n with
    | zero => simp [chemins, binom_self]
    | succ n ihn =>
      simp only [chemins]
      rw [ih (n + 1), ihn, show m + 1 + (n + 1) = (m + n + 1) + 1 by omega, binom_succ_succ,
        show m + (n + 1) = m + n + 1 by omega, show m + 1 + n = m + n + 1 by omega]

end Parcours.Combi

#verifier
