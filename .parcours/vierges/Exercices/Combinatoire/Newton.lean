import Exercices.Combinatoire.BinomBase

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

---
*Exercice* `Combinatoire.Newton` · difficulté ★★★★☆

💡 Indices : `./parcours indice Combinatoire.Newton` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

theorem binome (a b n : Nat) :
    (a + b) ^ n = somme (fun k => binom n k * a ^ k * b ^ (n - k)) (n + 1) := by
  sorry

end Parcours.Combi

#verifier
