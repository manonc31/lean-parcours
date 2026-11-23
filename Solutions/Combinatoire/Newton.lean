/- @parcours
celebre: 44
titre: Le binôme de Newton
difficulte: 4
indice: Récurrence sur `n`. Écris `(a+b)^(n+1) = a * (a+b)^n + b * (a+b)^n` et développe chaque morceau avec l'hypothèse de récurrence et `somme_mul`.
indice: Côté droit : `somme_decale` sort le terme `k = 0`, puis `binom_succ_succ` coupe chaque terme en deux (`somme_add`).
indice: Les termes en `binom n k * a^(k+1) * b^(n-k)` forment `a * (a+b)^n`. Les termes en `binom n (k+1) * …`, avec le terme `k = 0` (`b^(n+1)`), forment `b * (a+b)^n` (encore un `somme_decale`, et `binom n (n+1) = 0`).
indice: `somme_congr` permet d'ajuster les exposants terme à terme (`n + 1 - (k + 1) = n - k`), avec `omega` et `grind`.
-/
import Solutions.Combinatoire.BinomBase

/-!
# Le binôme de Newton

`(a + b)ⁿ = Σₖ C(n,k) aᵏ bⁿ⁻ᵏ`. Le triangle de Pascal donne les coefficients :
`(a+b)³ = a³ + 3a²b + 3ab² + b³`.

C'est la preuve la plus « calculatoire » du parcours jusqu'ici : il faut découper, décaler
et recoller des sommes. Prends ton temps et écris des lemmes intermédiaires (`have`).

## À prouver
`binome (a b n : Nat) : (a + b) ^ n = somme (fun k => binom n k * a ^ k * b ^ (n - k)) (n + 1)`

## Ressources
- [Formule du binôme de Newton (Wikipédia)](https://fr.wikipedia.org/wiki/Formule_du_bin%C3%B4me_de_Newton)
-/

namespace Parcours.Combi

theorem binome (a b n : Nat) :
    (a + b) ^ n = somme (fun k => binom n k * a ^ k * b ^ (n - k)) (n + 1) := by -- @exo
  induction n with
  | zero => simp [somme, binom]
  | succ n ih =>
    -- côté gauche
    have hg : (a + b) ^ (n + 1) = a * (a + b) ^ n + b * (a + b) ^ n := by
      rw [Nat.pow_succ]
      grind
    -- a * (a+b)^n
    have hA : a * (a + b) ^ n = somme (fun k => binom n k * a ^ (k + 1) * b ^ (n - k)) (n + 1) := by
      rw [ih, ← somme_mul]
      apply somme_congr
      intro k _
      rw [Nat.pow_succ]
      grind
    -- b * (a+b)^n
    have hB : b * (a + b) ^ n =
        b ^ (n + 1) + somme (fun k => binom n (k + 1) * a ^ (k + 1) * b ^ (n - k)) (n + 1) := by
      rw [ih, ← somme_mul, somme_decale, somme_succ (fun k => binom n (k + 1) * a ^ (k + 1) * b ^ (n - k)),
        binom_eq_zero (show n < n + 1 by omega)]
      have e : somme (fun k => b * (binom n (k + 1) * a ^ (k + 1) * b ^ (n - (k + 1)))) n =
          somme (fun k => binom n (k + 1) * a ^ (k + 1) * b ^ (n - k)) n := by
        apply somme_congr
        intro k hk
        rw [show n - k = (n - (k + 1)) + 1 by omega, Nat.pow_succ]
        grind
      rw [e, binom_zero_droite, Nat.pow_zero, Nat.sub_zero, Nat.pow_succ]
      grind
    -- côté droit : on sort le terme k = 0, puis on coupe chaque terme en deux (Pascal)
    have hD : somme (fun k => binom (n + 1) k * a ^ k * b ^ (n + 1 - k)) (n + 1 + 1) =
        b ^ (n + 1) + (somme (fun k => binom n k * a ^ (k + 1) * b ^ (n - k)) (n + 1) +
          somme (fun k => binom n (k + 1) * a ^ (k + 1) * b ^ (n - k)) (n + 1)) := by
      rw [somme_decale, ← somme_add]
      congr 1
      · simp [binom_zero_droite]
      · apply somme_congr
        intro k _
        rw [binom_succ_succ, show n + 1 - (k + 1) = n - k by omega]
        grind
    rw [hg, hA, hB, hD]
    omega

end Parcours.Combi

#verifier
