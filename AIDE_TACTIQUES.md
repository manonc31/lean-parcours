# 🧰 Aide-mémoire des tactiques Lean

Une preuve « en mode tactique » commence par `by`. Chaque tactique transforme le **but**
(ce qu'il reste à prouver, après `⊢` dans l'infoview) jusqu'à ce qu'il n'y en ait plus
(« No goals »).

## Taper les symboles
Dans VS Code, tape `\` puis le nom, et un espace :

| Symbole | Tape | Symbole | Tape |
|---|---|---|---|
| `→` | `\to` ou `\r` | `↔` | `\iff` |
| `∧` | `\and` | `∨` | `\or` |
| `¬` | `\not` | `≠` | `\ne` |
| `∀` | `\all` | `∃` | `\ex` |
| `≤` | `\le` | `≥` | `\ge` |
| `ℕ` | `\N` | `∣` (divise) | `\|` |
| `⟨ ⟩` | `\<` `\>` | `←` | `\l` |
| `∘` | `\comp` | `∈` | `\in` |
| `⁻¹` | `\inv` | `·` | `\.` |

Survole un symbole dans l'éditeur pour voir comment le taper.

---

## Les indispensables

| Tactique | Quand l'utiliser | Exemple |
|---|---|---|
| `rfl` | le but est `a = a` (ou vrai par calcul) | `example : 2 + 2 = 4 := by rfl` |
| `exact e` | `e` est exactement une preuve du but | `exact h` |
| `intro h` | le but est `P → Q` ou `∀ x, …` | `intro hp` |
| `apply h` | `h : P → Q` et le but est `Q` : il reste `P` | `apply hpq` |
| `rw [h]` | remplacer avec une égalité `h : a = b` (ou `↔`) | `rw [h1, ← h2]`, `rw [h] at h3` |
| `have h : P := …` | ajouter un fait intermédiaire | `have h2 := h1 5` |
| `show P` | réécrire le but sous une forme égale par définition | `show succ (a + b) = _` |
| `calc` | une chaîne d'égalités/inégalités pas à pas | voir Gymnase.Calc |

## Logique

| But / hypothèse | Pour **prouver** | Pour **utiliser** `h` |
|---|---|---|
| `P ∧ Q` | `constructor` ou `exact ⟨hp, hq⟩` | `h.1`, `h.2`, `obtain ⟨hp, hq⟩ := h` |
| `P ∨ Q` | `left` / `right` | `rcases h with hp \| hq` |
| `P → Q` | `intro hp` | `h hp` (appliquer) |
| `P ↔ Q` | `constructor` | `h.mp`, `h.mpr`, `rw [h]` |
| `¬P` | `intro hp` (puis prouver `False`) | `h hp : False` |
| `False` | — | `exact h.elim`, `contradiction` |
| `∀ x, P x` | `intro x` | `h a` |
| `∃ x, P x` | `exact ⟨a, preuve⟩` | `obtain ⟨x, hx⟩ := h` |
| `a = b` | `rfl`, `rw`, … | `rw [h]`, `h.symm`, `subst h` |

- `exfalso` : remplace le but par `False`.
- `contradiction` : trouve deux hypothèses contradictoires (ou `0 = n + 1`…).
- `by_cases h : P` : deux cas, `P` vrai ou faux (logique classique).
- `Classical.em P : P ∨ ¬P` ; `apply Classical.byContradiction` (raisonnement par l'absurde).
- `rintro ⟨hp, hq⟩` / `rintro (hp | hq)` : `intro` + `rcases` en une fois.
- `obtain ⟨c, rfl⟩ := h` : le `rfl` remplace directement la variable par sa valeur.

## Récurrence et cas

| Tactique | Effet |
|---|---|
| `induction n with \| zero => … \| succ n ih => …` | récurrence sur `n` |
| `induction n generalizing m with …` | l'hypothèse de récurrence vaut pour tout `m` |
| `cases n with \| zero => … \| succ m => …` | raisonnement par cas (sans hypothèse de récurrence) |
| `induction l with \| nil => … \| cons x l ih => …` | récurrence sur une liste |
| `induction n using Nat.strongRecOn with \| ind n ih => …` | récurrence forte sur `Nat` |
| `fun_induction f x with …` | récurrence qui suit les appels récursifs de `f` |
| `induction h with …` | récurrence sur une preuve d'une propriété inductive |
| `split` | sépare les cas d'un `if` ou d'un `match` dans le but |

Un **théorème récursif** est aussi une récurrence forte :
```lean
theorem t : (n : Nat) → P n
  | 0 => …
  | n + 2 => … t n …   -- appel sur un plus petit argument
```

## Automatisation (débloquée progressivement)

| Tactique | Ce qu'elle sait faire | Disponible ⭐ après |
|---|---|---|
| `decide` | vérifier par calcul un énoncé fini (sans variable libre) | tout de suite |
| `decide +kernel` | pareil, mais le calcul est fait directement par le noyau de Lean : bien plus rapide pour les gros calculs (huit reines, Kaprekar, RSA…) | tout de suite |
| `simp` | simplifier avec les lemmes de la bibliothèque | selon les ponts |
| `simp only [l1, l2]` | simplifier seulement avec les lemmes donnés | tout de suite (avec tes lemmes) |
| `omega` | arithmétique linéaire sur `Nat`/`Int` (`+`, `-`, `≤`, `%` et `/` par une constante) | Pont des entiers |
| `grind` | calcul algébrique (anneaux), égalités, un peu de logique | L'identité remarquable |
| `exact?` | **cherche** un lemme qui conclut | (propose souvent des lemmes de la bibliothèque) |

Astuces de calcul :
- `decide` ne sait pas calculer une fonction définie avec `termination_by` ; pour un calcul, on écrit
  plutôt une version avec une « réserve » (un compteur de pas) qui décroît structurellement.
- Pour vérifier un énoncé `∀ n, n < N → …` avec un très grand `N`, le noyau peut s'essouffler
  (« deep recursion ») : découpe en paquets, `∀ k, k < K → ∀ j, j < 100 → … (100 * k + j)`.
- Pour déplier une fonction définie avec `termination_by` dans une preuve : `rw [f]` (et pas `rfl`).

Combinateurs : `t1 <;> t2` (applique `t2` à tous les buts créés par `t1`), `·` pour traiter
un but à la fois, `try t` (essaie sans échouer), `all_goals t`.

## Commandes utiles (hors preuve)

- `#check add_comm` : affiche l'énoncé d'un théorème.
- `#eval 2 ^ 10` : calcule.
- `#print axioms mon_theoreme` : sur quels axiomes repose une preuve (`sorryAx` = pas fini !).

## Erreurs fréquentes

- **`unsolved goals`** : la preuve n'est pas finie ; regarde l'infoview à la fin de la preuve.
- **`rewrite failed, did not find instance of the pattern`** : le motif n'apparaît pas tel quel
  dans le but. Regarde la forme exacte (parenthèses ! `a + b + c` est `(a + b) + c`), ou utilise
  `show` pour réécrire le but sous une forme égale.
- **`type mismatch`** : le terme donné ne prouve pas exactement le but. Regarde les deux types affichés.
- **`unknown identifier`** : faute de frappe, ou lemme d'un autre fichier pas importé.
- Le nombre `2` dans `a ^ 2` avec `a : ℕ` (le ℕ de Peano) : écris `a ^ (2 : ℕ)`.
- Une tactique qui marchait dans un exercice échoue dans un autre : vérifie les **ponts** débloqués
  (l'infoview de `#verifier` te dit quels lemmes sont « empruntés »).
