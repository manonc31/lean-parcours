/- @parcours
titre: Le problème de l'arrêt est indécidable
difficulte: 3
requiert: Informatique.Lawvere
indice: Suppose un décideur `d`. Applique l'hypothèse `diagonale` à `d` : tu obtiens un programme `p` qui s'arrête sur `q` exactement quand `d q q = false`.
indice: Regarde ce qui se passe pour `q = p` : `cases hdp : d p p`, puis `simp_all`.
-/
import Solutions.Informatique.Expressions

/-!
# Le problème de l'arrêt est indécidable

Existe-t-il un programme qui, étant donné un programme `p` et une entrée `q`, dit si `p` s'arrête
sur `q` ? Turing (1936) : **non**.

On modélise un langage de programmation de façon abstraite : un type `Prog` de programmes,
et `arrete p q` (« `p` s'arrête sur l'entrée `q` »). La seule hypothèse : le langage est assez riche
pour, à partir de **n'importe quel** décideur `d`, écrire le programme « diagonal » qui s'arrête
sur `q` exactement quand `d` répond « non » sur `(q, q)` (une boucle infinie si `d` dit « oui »).

## À prouver
`arret_indecidable : ¬∃ d : Prog → Prog → Bool, ∀ p q, d p q = true ↔ arrete p q`

## Ressources
- [Problème de l'arrêt (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_de_l%27arr%C3%AAt)
-/

namespace Parcours.Info

theorem arret_indecidable {Prog : Type} (arrete : Prog → Prog → Prop)
    (diagonale : ∀ d : Prog → Prog → Bool, ∃ p, ∀ q, arrete p q ↔ d q q = false) :
    ¬∃ d : Prog → Prog → Bool, ∀ p q, d p q = true ↔ arrete p q := by -- @exo
  rintro ⟨d, hd⟩
  obtain ⟨p, hp⟩ := diagonale d
  have h1 := hd p p
  have h2 := hp p
  cases hdp : d p p <;> simp_all

end Parcours.Info

#verifier
