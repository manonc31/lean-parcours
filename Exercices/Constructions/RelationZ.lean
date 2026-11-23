import Exercices.Recurrence.Definitions

/-!
# La relation qui définit ℤ

Comment construire les entiers **relatifs** quand on n'a que les naturels ? Idée : un couple
`(a, b)` représente « `a - b` ». Mais `(5, 2)` et `(4, 1)` représentent le même entier `3` !
On les identifie avec la relation :

`(a, b) ~ (c, d)  ⟺  a + d = c + b`   (c'est « `a - b = c - d` » sans soustraction)

Pour faire un **quotient** (identifier les couples équivalents), il faut que `~` soit une
relation d'**équivalence** : réflexive, symétrique, transitive. C'est ton travail.

## À prouver
1. `relZ_refl : RelZ p p`
2. `relZ_symm : RelZ p q → RelZ q p`
3. `relZ_trans : RelZ p q → RelZ q r → RelZ p r`

## Ressources
- [Construction des entiers relatifs (Wikipédia)](https://fr.wikipedia.org/wiki/Construction_des_entiers_relatifs)
- [Relation d'équivalence (Wikipédia)](https://fr.wikipedia.org/wiki/Relation_d%27%C3%A9quivalence)

---
*Exercice* `Constructions.RelationZ` · difficulté ★★☆☆☆

💡 Indices : `./parcours indice Constructions.RelationZ` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Constructions

/-- `(a, b)` représente l'entier relatif `a - b`. -/
def RelZ (p q : Nat × Nat) : Prop := p.1 + q.2 = q.1 + p.2

theorem relZ_refl (p : Nat × Nat) : RelZ p p := by
  sorry

theorem relZ_symm {p q : Nat × Nat} (h : RelZ p q) : RelZ q p := by
  sorry

theorem relZ_trans {p q r : Nat × Nat} (h1 : RelZ p q) (h2 : RelZ q r) : RelZ p r := by
  sorry

end Parcours.Constructions

#verifier
