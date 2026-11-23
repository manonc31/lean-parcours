import Exercices.Combinatoire.Definitions

/-!
# Cinq invités ne suffisent pas (Ramsey)

> Dans toute soirée de 6 personnes, il y en a 3 qui se connaissent toutes, ou 3 qui ne se
> connaissent pas du tout. (C'est le boss suivant.)

Ici : montre que **5** personnes ne suffisent pas, en exhibant un contre-exemple.
Une « soirée » est une fonction `c : Fin 5 → Fin 5 → Bool` symétrique (`c i j = true` : `i` et `j`
se connaissent). Un triangle monochrome est un triple de personnes distinctes avec les trois
relations de même couleur.

Nouveauté : **`decide`** vérifie automatiquement un énoncé quand il n'y a qu'un nombre fini de cas.

## À prouver
`ramsey_cinq : ∃ c : Fin 5 → Fin 5 → Bool, (∀ i j, c i j = c j i) ∧
  ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ¬(c i j = c j k ∧ c j k = c i k)`

## Ressources
- [Théorème de Ramsey (Wikipédia)](https://fr.wikipedia.org/wiki/Th%C3%A9or%C3%A8me_de_Ramsey)

---
*Exercice* `Combinatoire.Ramsey5` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Combinatoire.Ramsey5` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Combi

theorem ramsey_cinq : ∃ c : Fin 5 → Fin 5 → Bool, (∀ i j, c i j = c j i) ∧
    ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ¬(c i j = c j k ∧ c j k = c i k) := by
  sorry

end Parcours.Combi

#verifier
