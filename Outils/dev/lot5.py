import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

P = "Solutions.Programmes.Definitions"
NS = "Parcours.Prog"

def pr(ident, titre, diff, texte, code, indices, requiert, imports=(P,), ressources=(), celebre=0):
    exo("Programmes", ident, titre, diff, list(imports), texte, code, indices, NS,
        requiert=requiert, ressources=ressources, celebre=celebre)

pr("Accumulateur", "Additionner avec un accumulateur", 1,
"""Un programme qui additionne une liste « comme à la main » : on garde un total partiel `acc`
(l'**accumulateur**) et on lui ajoute les éléments un par un. C'est ce que fait une boucle `for`.

Le piège : pour la récurrence, il faut que l'énoncé parle de **n'importe quel** accumulateur de
départ, pas seulement de `0`.

## À prouver
1. `sommeAcc_spec : sommeAcc l acc = acc + l.sum`
2. `sommeAcc_zero : sommeAcc l 0 = l.sum`""",
"""def sommeAcc : List Nat → Nat → Nat
  | [], acc => acc
  | x :: l, acc => sommeAcc l (acc + x)

theorem sommeAcc_spec (l : List Nat) (acc : Nat) : sommeAcc l acc = acc + l.sum := by -- @exo
  induction l generalizing acc with
  | nil => simp [sommeAcc]
  | cons x l ih =>
    simp only [sommeAcc, ih, List.sum_cons]
    omega

theorem sommeAcc_zero (l : List Nat) : sommeAcc l 0 = l.sum := by -- @exo
  rw [sommeAcc_spec, Nat.zero_add]""",
["`induction l generalizing acc` : l'hypothèse de récurrence vaudra pour tout accumulateur.", "`simp only [sommeAcc, ih, List.sum_cons]` puis `omega`."], "Programmes.Definitions")

pr("Compter", "Compter les occurrences", 2,
"""`compter a l` compte combien de fois `a` apparaît dans `l`.

## À prouver
1. `compter_append : compter a (l₁ ++ l₂) = compter a l₁ + compter a l₂`
2. `compter_le : compter a l ≤ l.length`
3. `compter_pos : 0 < compter a l ↔ a ∈ l`""",
"""def compter (a : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => (if x = a then 1 else 0) + compter a l

theorem compter_append (a : Nat) (l₁ l₂ : List Nat) :
    compter a (l₁ ++ l₂) = compter a l₁ + compter a l₂ := by -- @exo
  induction l₁ with
  | nil => simp [compter]
  | cons x l ih =>
    simp only [List.cons_append, compter, ih]
    omega

theorem compter_le (a : Nat) (l : List Nat) : compter a l ≤ l.length := by -- @exo
  induction l with
  | nil => simp [compter]
  | cons x l ih =>
    simp only [compter, List.length_cons]
    split <;> omega

theorem compter_pos (a : Nat) (l : List Nat) : 0 < compter a l ↔ a ∈ l := by -- @exo
  induction l with
  | nil => simp [compter]
  | cons x l ih =>
    simp only [compter, List.mem_cons]
    by_cases h : x = a
    · subst h
      simp only [↓reduceIte, true_or, iff_true]
      omega
    · simp only [h, ↓reduceIte, Nat.zero_add, ih]
      constructor
      · intro h'
        exact Or.inr h'
      · rintro (h' | h')
        · exact absurd h'.symm h
        · exact h'""",
["Récurrence sur la liste ; `simp only [compter]` déplie la définition.", "Pour un `if`, `split` sépare les deux cas, ou `by_cases h : x = a` puis `if_pos h` / `if_neg h`."], "Programmes.Accumulateur")

pr("FizzBuzz", "FizzBuzz", 1,
"""Le célèbre test d'entretien d'embauche : pour chaque nombre, afficher « Fizz » s'il est multiple
de 3, « Buzz » s'il est multiple de 5, « FizzBuzz » s'il est multiple des deux, et le nombre sinon.
Ici, la sortie est un petit type `Sortie` plutôt qu'une chaîne de caractères.

## À prouver
1. `fb_quinze : fb (15 * k) = .fizzbuzz`
2. `fb_fizz : fb n = .fizz ↔ n % 3 = 0 ∧ n % 5 ≠ 0`
3. `fizz_cent` : entre 1 et 100, il y a exactement 27 « Fizz ».""",
"""inductive Sortie where
  | fizz
  | buzz
  | fizzbuzz
  | nombre (n : Nat)
  deriving DecidableEq

def fb (n : Nat) : Sortie :=
  if n % 15 = 0 then .fizzbuzz
  else if n % 3 = 0 then .fizz
  else if n % 5 = 0 then .buzz
  else .nombre n

theorem fb_quinze (k : Nat) : fb (15 * k) = .fizzbuzz := by -- @exo
  simp [fb]

theorem fb_fizz (n : Nat) : fb n = .fizz ↔ n % 3 = 0 ∧ n % 5 ≠ 0 := by -- @exo
  unfold fb
  repeat' split
  all_goals simp
  all_goals omega

theorem fizz_cent : ((List.range 100).filter (fun n => fb (n + 1) = .fizz)).length = 27 := by -- @exo
  decide""",
["`fb_quinze` : `simp [fb]` sait que `15 * k % 15 = 0`.", "`fb_fizz` : `unfold fb`, puis `repeat' split` pour casser tous les `if` ; dans chaque cas `simp` puis `omega`.", "`fizz_cent` : c'est un calcul, `decide`."], "Programmes.Definitions",
ressources=["[FizzBuzz (Rosetta Code)](https://rosettacode.org/wiki/FizzBuzz)"])

pr("Cesar", "Le chiffre de César", 2,
"""Jules César chiffrait ses messages en décalant chaque lettre de 3 dans l'alphabet : A → D,
B → E, …, Z → C. Les lettres sont ici des nombres de 0 à 25, et le décalage se fait modulo 26.
« HELLO » = `[7, 4, 11, 11, 14]` devient « KHOOR ».

## À prouver
1. `cesar_compose : cesar a (cesar b m) = cesar (a + b) m` (deux décalages font un décalage)
2. `cesar_dechiffre` : décaler de `26 - k` annule un décalage de `k` (pour un vrai message)
3. `rot13` : ROT13 (décalage de 13, utilisé sur les forums pour cacher les spoilers !) est son
   propre inverse.
4. `hello : cesar 3 [7, 4, 11, 11, 14] = [10, 7, 14, 14, 17]`""",
"""def decaler (k x : Nat) : Nat := (x + k) % 26

def cesar (k : Nat) (m : List Nat) : List Nat := m.map (decaler k)

theorem cesar_compose (a b : Nat) (m : List Nat) : cesar a (cesar b m) = cesar (a + b) m := by -- @exo
  simp only [cesar, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply, decaler]
  omega

theorem cesar_dechiffre (k : Nat) (m : List Nat) (h : ∀ x ∈ m, x < 26) :
    cesar (26 - k % 26) (cesar k m) = m := by -- @exo
  rw [cesar_compose]
  conv => rhs; rw [← List.map_id m]
  apply List.map_congr_left
  intro x hx
  have := h x hx
  simp only [decaler, id]
  omega

theorem rot13 (m : List Nat) (h : ∀ x ∈ m, x < 26) : cesar 13 (cesar 13 m) = m := by -- @exo
  simpa using cesar_dechiffre 13 m h

theorem hello : cesar 3 [7, 4, 11, 11, 14] = [10, 7, 14, 14, 17] := by -- @exo
  decide""",
["`List.map_map` fusionne deux `map`, et `List.map_congr_left` permet de comparer deux `map` élément par élément.", "Sur chaque élément, il reste une égalité avec des `% 26` : `omega`.", "Pour `cesar_dechiffre`, écris `m` comme `List.map id m` (`← List.map_id`)."], "Programmes.Accumulateur",
ressources=["[Chiffrement par décalage (Wikipédia)](https://fr.wikipedia.org/wiki/Chiffrement_par_d%C3%A9calage)"])

pr("Vernam", "Le masque jetable", 2,
"""Le **masque jetable** (Vernam, 1917) est le seul chiffrement **parfaitement sûr** : on combine
chaque bit du message avec un bit d'une clé aléatoire aussi longue que le message, par OU
exclusif (`^^`). Pour déchiffrer, on refait la même opération avec la même clé.

Pourquoi est-il parfaitement sûr ? Parce que **n'importe quel** message aurait pu donner le
chiffré observé, avec une clé bien choisie : l'espion n'apprend rien.

## À prouver
1. `masque_involutif : masque k (masque k m) = m` (si `k` et `m` ont la même longueur)
2. `masque_secret : masque (masque m c) m = c` : pour tout message `m` et tout chiffré `c`,
   la clé `masque m c` transforme `m` en `c`.""",
"""def masque : List Bool → List Bool → List Bool
  | k :: ks, m :: ms => (k ^^ m) :: masque ks ms
  | _, _ => []

theorem masque_involutif (k m : List Bool) (h : k.length = m.length) :
    masque k (masque k m) = m := by -- @exo
  induction k generalizing m with
  | nil =>
    cases m with
    | nil => rfl
    | cons => simp at h
  | cons a k ih =>
    cases m with
    | nil => simp at h
    | cons b m =>
      simp only [masque]
      rw [ih m (by simpa using h)]
      cases a <;> cases b <;> rfl

theorem masque_secret (m c : List Bool) (h : m.length = c.length) :
    masque (masque m c) m = c := by -- @exo
  induction m generalizing c with
  | nil =>
    cases c with
    | nil => rfl
    | cons => simp at h
  | cons a m ih =>
    cases c with
    | nil => simp at h
    | cons b c =>
      simp only [masque]
      rw [ih c (by simpa using h)]
      cases a <;> cases b <;> rfl""",
["Récurrence sur `k` en généralisant `m`, puis `cases m`.", "Les cas où les longueurs diffèrent sont absurdes : `simp at h`.", "Pour les bits : `cases a <;> cases b <;> rfl`."], "Programmes.Cesar",
ressources=["[Masque jetable (Wikipédia)](https://fr.wikipedia.org/wiki/Masque_jetable)"])

pr("Russe", "La multiplication russe", 2,
"""La multiplication « du paysan russe » (ou égyptienne) : pour calculer `a × b`, on divise `a` par 2
et on double `b`, jusqu'à ce que `a` vaille 0 ; on additionne les `b` des lignes où `a` est
impair.

```
 13 × 7
  6 × 14   (pair : on barre)
  3 × 28
  1 × 56
 → 7 + 28 + 56 = 91
```
C'est exactement la multiplication en binaire, et la façon dont les processeurs multiplient.

## À prouver
`russe_spec : russe a b = a * b`""",
"""def russe (a b : Nat) : Nat :=
  if a = 0 then 0
  else if a % 2 = 0 then russe (a / 2) (2 * b)
  else b + russe (a / 2) (2 * b)
termination_by a
decreasing_by all_goals omega

theorem russe_spec (a b : Nat) : russe a b = a * b := by -- @exo
  fun_induction russe a b with
  | case1 b => simp
  | case2 a b h1 h2 ih =>
    rw [ih]
    have e : a = 2 * (a / 2) := by omega
    conv => rhs; rw [e]
    generalize a / 2 = q
    grind
  | case3 a b h1 h2 ih =>
    rw [ih]
    have e : a = 2 * (a / 2) + 1 := by omega
    conv => rhs; rw [e]
    generalize a / 2 = q
    grind""",
["`fun_induction russe a b` : trois cas (a = 0, a pair, a impair), avec l'hypothèse de récurrence pour `russe (a / 2) (2 * b)`.", "Écris `a = 2 * (a / 2)` (ou `+ 1`) grâce à `omega`, puis `generalize a / 2 = q` et `grind`."], "Programmes.Definitions",
ressources=["[Multiplication égyptienne (Wikipédia)](https://fr.wikipedia.org/wiki/Technique_de_la_multiplication_%C3%A9gyptienne)"])

pr("DivisionSoustraction", "Diviser en soustrayant", 2,
"""Comment diviser quand on ne sait que soustraire ? On retire `b` de `a` tant qu'on peut, en
comptant les retraits : le nombre de retraits est le quotient, ce qui reste est le reste.

## À prouver
1. `divSous_spec : q * b + r = a ∧ r < b` où `(q, r) = divSous a b` (si `b > 0`)
2. `divSous_quotient : (divSous a b).1 = a / b`""",
"""def divSous (a b : Nat) : Nat × Nat :=
  if _ : 0 < b ∧ b ≤ a then ((divSous (a - b) b).1 + 1, (divSous (a - b) b).2) else (0, a)
termination_by a
decreasing_by omega

theorem divSous_spec (a b : Nat) (hb : 0 < b) :
    (divSous a b).1 * b + (divSous a b).2 = a ∧ (divSous a b).2 < b := by -- @exo
  fun_induction divSous a b with
  | case1 a h ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only
    rw [Nat.add_mul, Nat.one_mul]
    omega
  | case2 a h =>
    dsimp only
    omega

theorem divSous_quotient (a b : Nat) (hb : 0 < b) : (divSous a b).1 = a / b := by -- @exo
  obtain ⟨h1, h2⟩ := divSous_spec a b hb
  conv => rhs; rw [← h1]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt h2, Nat.zero_add]""",
["`fun_induction divSous a b` : un cas « on peut soustraire », un cas « on s'arrête ».", "Dans le premier cas : `(q + 1) * b = q * b + b` (`Nat.add_mul`), puis `omega`.", "Pour le quotient : réécris `a` en `q * b + r`, puis `Nat.add_mul_div_right` et `Nat.div_eq_of_lt`."], "Programmes.Russe")

pr("RacineEntiere", "La racine carrée entière", 3,
"""`racine n` est le plus grand entier `r` tel que `r² ≤ n`. Le programme essaie `n, n − 1, …`
jusqu'à trouver un `r` qui convient (lent, mais facile à prouver !).

## À prouver
1. `racineAux_le : (racineAux n k)² ≤ n`
2. `racineAux_lt : n < (k + 1)² → n < (racineAux n k + 1)²`
3. `racine_spec : r * r ≤ n ∧ n < (r + 1) * (r + 1)` où `r = racine n`
4. `racine_mille : racine 1000 = 31`""",
"""def racineAux (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if (k + 1) * (k + 1) ≤ n then k + 1 else racineAux n k

def racine (n : Nat) : Nat := racineAux n n

theorem racineAux_le (n k : Nat) : racineAux n k * racineAux n k ≤ n := by -- @exo
  induction k with
  | zero => simp [racineAux]
  | succ k ih =>
    simp only [racineAux]
    split <;> assumption

theorem racineAux_lt (n k : Nat) (h : n < (k + 1) * (k + 1)) :
    n < (racineAux n k + 1) * (racineAux n k + 1) := by -- @exo
  induction k with
  | zero => simpa [racineAux] using h
  | succ k ih =>
    simp only [racineAux]
    split
    · exact h
    · rename_i h'
      exact ih (Nat.not_le.mp h')

theorem racine_spec (n : Nat) :
    racine n * racine n ≤ n ∧ n < (racine n + 1) * (racine n + 1) := by -- @exo
  refine ⟨racineAux_le n n, racineAux_lt n n ?_⟩
  have : n + 1 ≤ (n + 1) * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem racine_mille : racine 1000 = 31 := by -- @exo
  decide +kernel""",
["Pour `racineAux_le` : récurrence sur `k`, `simp only [racineAux]`, `split` ; dans les deux cas, c'est une hypothèse.", "Pour `racineAux_lt` : dans le cas « else », la condition est fausse : `Nat.not_le.mp` donne `n < (k + 1) * (k + 1)`.", "Pour `racine_spec`, il reste à voir `n < (n + 1) * (n + 1)` : `Nat.le_mul_of_pos_right`."], "Programmes.DivisionSoustraction")

pr("Chiffres", "Le nombre de chiffres", 2,
"""Combien de chiffres a un nombre en base 10 ? On divise par 10 jusqu'à tomber sous 10.
La spécification : un nombre à `c` chiffres est entre `10^(c−1)` et `10^c`.

## À prouver
1. `nbChiffres_pos : 1 ≤ nbChiffres n`
2. `lt_puissance : n < 10 ^ nbChiffres n`
3. `puissance_le : 0 < n → 10 ^ (nbChiffres n - 1) ≤ n`""",
"""def nbChiffres (n : Nat) : Nat := if n < 10 then 1 else nbChiffres (n / 10) + 1
termination_by n
decreasing_by omega

theorem nbChiffres_pos (n : Nat) : 1 ≤ nbChiffres n := by -- @exo
  fun_induction nbChiffres n <;> omega

theorem lt_puissance (n : Nat) : n < 10 ^ nbChiffres n := by -- @exo
  fun_induction nbChiffres n with
  | case1 n h => simpa using h
  | case2 n h ih =>
    rw [Nat.pow_succ]
    omega

theorem puissance_le (n : Nat) (h : 0 < n) : 10 ^ (nbChiffres n - 1) ≤ n := by -- @exo
  fun_induction nbChiffres n with
  | case1 n _ =>
    simp only [Nat.sub_self, Nat.pow_zero]
    omega
  | case2 n h' ih =>
    have ih := ih (by omega)
    obtain ⟨c, hc⟩ : ∃ c, nbChiffres (n / 10) = c + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (nbChiffres_pos (n / 10))).symm⟩
    rw [hc] at ih ⊢
    simp only [Nat.add_sub_cancel] at ih ⊢
    rw [Nat.pow_succ]
    omega""",
["`fun_induction nbChiffres n` : deux cas, `n < 10` et le cas récursif.", "`Nat.pow_succ : a ^ (n + 1) = a ^ n * a`, puis `omega` (il traite `10 ^ c` comme une inconnue).", "Pour `puissance_le`, écris `nbChiffres (n / 10) = c + 1` (grâce à `nbChiffres_pos`)."], "Programmes.Definitions")

pr("Onze", "La règle de divisibilité par 11", 3,
"""Pour savoir si un nombre est divisible par 11, on fait la somme **alternée** de ses chiffres en
partant des unités : `918082 → 2 − 8 + 0 − 8 + 1 − 9 = −22`, divisible par 11, donc 918082 aussi.
Pourquoi ? Parce que `10 ≡ −1 (mod 11)`.

## À prouver
1. `onze_alterne : (n - alterne n) % 11 = 0` (dans `Int`)
2. `onze_divise : n % 11 = 0 ↔ alterne n % 11 = 0`""",
"""def alterne (n : Nat) : Int := if n < 10 then n else ((n % 10 : Nat) : Int) - alterne (n / 10)
termination_by n
decreasing_by omega

theorem onze_alterne (n : Nat) : ((n : Int) - alterne n) % 11 = 0 := by -- @exo
  fun_induction alterne n with
  | case1 n _ => simp
  | case2 n _ ih => omega

theorem onze_divise (n : Nat) : n % 11 = 0 ↔ alterne n % 11 = 0 := by -- @exo
  have := onze_alterne n
  omega""",
["`fun_induction alterne n`. Dans le cas récursif, `n = 10 * (n / 10) + n % 10` : `omega` voit tout seul que la différence est un multiple de 11.", "`omega` connaît les conversions `Nat → Int` et les `%` par des constantes."], "Programmes.Chiffres")

pr("Bases", "Changer de base", 3,
"""Écrire un nombre en base `b` : les chiffres sont les restes successifs de la division par `b`
(chiffre des unités en tête). Puis relire la liste de chiffres pour retrouver le nombre.
`versBase 2 13 = [1, 0, 1, 1]` (car 13 = 1101 en binaire).

## À prouver
1. `aller_retour : depuisBase b (versBase b n) = n` (pour `b ≥ 2`)
2. `chiffres_petits : d ∈ versBase b n → d < b`""",
"""def versBase (b n : Nat) : List Nat :=
  if h : 2 ≤ b ∧ 0 < n then n % b :: versBase b (n / b) else []
termination_by n
decreasing_by exact Nat.div_lt_self h.2 (by omega)

def depuisBase (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: l => d + b * depuisBase b l

theorem aller_retour (b n : Nat) (hb : 2 ≤ b) : depuisBase b (versBase b n) = n := by -- @exo
  fun_induction versBase b n with
  | case1 n h ih =>
    simp only [depuisBase, ih]
    exact Nat.mod_add_div n b
  | case2 n h =>
    simp only [depuisBase]
    omega

theorem chiffres_petits (b n : Nat) : ∀ d ∈ versBase b n, d < b := by -- @exo
  fun_induction versBase b n with
  | case1 n h ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact Nat.mod_lt _ (by omega)
    · exact ih d hd
  | case2 n h => simp""",
["`fun_induction versBase b n` : deux cas.", "`Nat.mod_add_div n b : n % b + b * (n / b) = n`.", "Pour `chiffres_petits` : `Nat.mod_lt`."], "Programmes.Chiffres")

pr("ExpModulaire", "L'exponentiation modulaire", 3,
"""Pour calculer `a^n mod m` avec des nombres géants (c'est le cœur de RSA), on ne calcule jamais
`a^n` : on réduit modulo `m` à chaque étape, et on utilise `a^(2k) = (a^k)²`.

## À prouver
`expMod_spec : expMod a n m = a ^ n % m`""",
"""def expMod (a n m : Nat) : Nat :=
  if n = 0 then 1 % m
  else if n % 2 = 0 then (expMod a (n / 2) m * expMod a (n / 2) m) % m
  else (expMod a (n / 2) m * expMod a (n / 2) m * a) % m
termination_by n
decreasing_by all_goals omega

theorem expMod_spec (a n m : Nat) : expMod a n m = a ^ n % m := by -- @exo
  fun_induction expMod a n m with
  | case1 => simp
  | case2 n h1 h2 ih =>
    rw [ih, ← Nat.mul_mod, ← Nat.pow_add]
    congr 2
    omega
  | case3 n h1 h2 ih =>
    rw [ih, Nat.mul_mod, ← Nat.mul_mod (a ^ (n / 2)), ← Nat.mul_mod, ← Nat.pow_add, ← Nat.pow_succ]
    congr 2
    omega""",
["`fun_induction expMod a n m` : trois cas.", "`Nat.mul_mod : a * b % n = (a % n) * (b % n) % n` (à utiliser de droite à gauche), `Nat.pow_add`, `Nat.pow_succ`.", "À la fin, `n / 2 + n / 2 = n` (ou `+ 1`) : `congr 2` puis `omega`."], "Programmes.Russe",
ressources=["[Exponentiation modulaire (Wikipédia)](https://fr.wikipedia.org/wiki/Exponentiation_modulaire)"])

pr("Bissextile", "Les années bissextiles", 1,
"""Une année est bissextile si elle est divisible par 4, sauf les siècles, sauf les multiples
de 400 : 2000 l'était, 1900 non, 2024 oui. Le calendrier grégorien se répète tous les 400 ans…
et 400 ans font **exactement** un nombre entier de semaines ! (Donc le 1er janvier 2400 sera un
samedi, comme le 1er janvier 2000.)

## À prouver
1. `an2000`, `an1900` : 2000 est bissextile, 1900 ne l'est pas.
2. `periode : bissextile (a + 400) = bissextile a`
3. `quatre_cents_ans` : 97 années bissextiles sur 400 ans.
4. `semaines` : 400 ans font 146 097 jours, un multiple de 7.""",
"""def bissextile (a : Nat) : Bool := (a % 4 == 0 && a % 100 != 0) || a % 400 == 0

def jours (a : Nat) : Nat := if bissextile a then 366 else 365

theorem an2000 : bissextile 2000 = true := by -- @exo
  decide

theorem an1900 : bissextile 1900 = false := by -- @exo
  decide

theorem periode (a : Nat) : bissextile (a + 400) = bissextile a := by -- @exo
  have h1 : (a + 400) % 4 = a % 4 := by omega
  have h2 : (a + 400) % 100 = a % 100 := by omega
  have h3 : (a + 400) % 400 = a % 400 := by omega
  simp only [bissextile, h1, h2, h3]

theorem quatre_cents_ans : ((List.range 400).filter bissextile).length = 97 := by -- @exo
  decide

theorem semaines : ((List.range 400).map jours).sum = 146097 ∧ 146097 % 7 = 0 := by -- @exo
  decide +kernel""",
["Les calculs sur des valeurs précises : `decide` (ou `decide +kernel` si c'est gros).", "Pour `periode` : `(a + 400) % 4 = a % 4` (`omega`), pareil pour 100 et 400, puis `simp only [bissextile, …]`."], "Programmes.FizzBuzz",
ressources=["[Année bissextile (Wikipédia)](https://fr.wikipedia.org/wiki/Ann%C3%A9e_bissextile)"])

pr("Recherche", "Chercher dans une liste", 1,
"""`chercher p l` renvoie le premier élément de `l` qui vérifie `p` (ou `none` s'il n'y en a pas).

## À prouver
1. `chercher_some` : si on trouve `x`, alors `x ∈ l` et `p x`.
2. `chercher_none` : si on ne trouve rien, aucun élément ne vérifie `p`.""",
"""def chercher (p : Nat → Bool) : List Nat → Option Nat
  | [] => none
  | x :: l => if p x then some x else chercher p l

theorem chercher_some (p : Nat → Bool) (l : List Nat) (x : Nat) (h : chercher p l = some x) :
    x ∈ l ∧ p x = true := by -- @exo
  induction l with
  | nil => simp [chercher] at h
  | cons y l ih =>
    simp only [chercher] at h
    split at h
    · rename_i hy
      cases h
      exact ⟨List.mem_cons_self, hy⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem chercher_none (p : Nat → Bool) (l : List Nat) (h : chercher p l = none) :
    ∀ x ∈ l, p x = false := by -- @exo
  induction l with
  | nil => simp
  | cons y l ih =>
    simp only [chercher] at h
    split at h
    · simp at h
    · rename_i hy
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa using hy
      · exact ih h x hx""",
["Récurrence sur `l`, et `split at h` pour séparer les cas du `if` dans l'hypothèse.", "`some y = some x` : `cases h` remplace `x` par `y`."], "Programmes.Accumulateur")

pr("Parentheses", "Les parenthèses bien équilibrées", 3,
"""Un éditeur de code vérifie que les parenthèses sont bien équilibrées avec un simple
**compteur** : +1 pour « ( », −1 pour « ) », le compteur ne doit jamais devenir négatif et doit
finir à 0. (Ici `true` = « ( » et `false` = « ) ».)

Mais qu'est-ce qu'un « bon parenthésage » ? La définition mathématique est **inductive** : le mot
vide, `( mot )`, ou deux bons mots à la suite. Il faut prouver que le compteur accepte tous les
bons mots.

## À prouver
1. `verif_append` : un bon mot ne change pas l'état du compteur.
2. `verif_correct : BienParenthese l → verif l 0 = true`
3. `exemples` : `(()())` est accepté, `())(` est refusé.""",
"""inductive BienParenthese : List Bool → Prop
  | vide : BienParenthese []
  | entoure {l : List Bool} : BienParenthese l → BienParenthese (true :: l ++ [false])
  | concat {l₁ l₂ : List Bool} : BienParenthese l₁ → BienParenthese l₂ → BienParenthese (l₁ ++ l₂)

def verif : List Bool → Nat → Bool
  | [], c => c == 0
  | true :: l, c => verif l (c + 1)
  | false :: l, c => c != 0 && verif l (c - 1)

theorem verif_append (l : List Bool) (h : BienParenthese l) :
    ∀ (r : List Bool) (c : Nat), verif (l ++ r) c = verif r c := by -- @exo
  induction h with
  | vide => intro r c; rfl
  | entoure _ ih =>
    intro r c
    simp only [List.cons_append, List.append_assoc, verif]
    rw [ih]
    simp [verif]
  | concat _ _ ih₁ ih₂ =>
    intro r c
    rw [List.append_assoc, ih₁, ih₂]

theorem verif_correct (l : List Bool) (h : BienParenthese l) : verif l 0 = true := by -- @exo
  have := verif_append l h [] 0
  simpa [verif] using this

theorem exemples : verif [true, true, false, true, false, false] 0 = true ∧
    verif [true, false, false, true] 0 = false := by -- @exo
  decide""",
["Récurrence sur la preuve `h : BienParenthese l` (`induction h`), avec un énoncé qui parle de tout ce qui suit (`r`) et de tout compteur `c`.", "Cas `entoure` : `true :: (l ++ ([false] ++ r))` ; le compteur monte, `l` ne le change pas, `false` le redescend."], "Programmes.Recherche")

pr("Reines", "Le problème des huit reines", 2,
"""Placer 8 reines sur un échiquier sans qu'aucune n'en menace une autre (ni même ligne, ni même
colonne, ni même diagonale). Gauss lui-même s'y est cassé les dents ! Une solution est une liste :
la reine de la ligne `i` est dans la colonne `l[i]`.

`placer n k` construit **toutes** les façons de placer `k` reines compatibles sur les `k`
premières lignes d'un échiquier `n × n` (c'est l'algorithme de **retour sur trace** :
on ajoute une reine seulement si elle est compatible avec les précédentes).

## À prouver
1. `une_solution : [0, 4, 7, 5, 2, 6, 1, 3] ∈ placer 8 8`
2. `quatre_vingt_douze` : il y a exactement 92 solutions.
3. `trois_impossible` : aucune solution pour 3 reines.""",
"""def compatible (p : List Nat) (c : Nat) : Bool :=
  (List.range p.length).all fun i =>
    p.getD i 0 != c && i + c != p.length + p.getD i 0 && i + p.getD i 0 != p.length + c

def placer (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (placer n k).flatMap fun p =>
      ((List.range n).filter fun c => compatible p c).map fun c => p ++ [c]

theorem une_solution : [0, 4, 7, 5, 2, 6, 1, 3] ∈ placer 8 8 := by -- @exo
  decide +kernel

theorem quatre_vingt_douze : (placer 8 8).length = 92 := by -- @exo
  decide +kernel

theorem trois_impossible : placer 3 3 = [] := by -- @exo
  decide""",
["Ce sont des calculs : `decide`, ou `decide +kernel` pour les plus gros (le noyau de Lean fait des milliers de calculs).", "Essaie `#eval placer 6 6` pour voir les 4 solutions sur un échiquier 6 × 6."], "Programmes.Recherche",
ressources=["[Problème des huit dames (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_des_huit_dames)"])

pr("Dedoublonner", "Supprimer les doublons", 2,
"""`dedup` garde un seul exemplaire de chaque élément (le dernier).

## À prouver
1. `mem_dedup : x ∈ dedup l ↔ x ∈ l` (on n'a rien perdu)
2. `nodup_dedup : (dedup l).Nodup` (plus aucun doublon)""",
"""def dedup : List Nat → List Nat
  | [] => []
  | x :: l => if x ∈ l then dedup l else x :: dedup l

theorem mem_dedup (x : Nat) (l : List Nat) : x ∈ dedup l ↔ x ∈ l := by -- @exo
  induction l with
  | nil => simp [dedup]
  | cons y l ih =>
    simp only [dedup]
    split
    · rename_i h
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h')
        · exact h
        · exact h'
    · rw [List.mem_cons, ih, List.mem_cons]

theorem nodup_dedup (l : List Nat) : (dedup l).Nodup := by -- @exo
  induction l with
  | nil => simp [dedup]
  | cons y l ih =>
    simp only [dedup]
    split
    · exact ih
    · rename_i h
      rw [List.nodup_cons, mem_dedup]
      exact ⟨h, ih⟩""",
["Récurrence sur `l`, puis `split` sur le `if x ∈ l`.", "`List.nodup_cons : (a :: l).Nodup ↔ a ∉ l ∧ l.Nodup`."], "Programmes.Compter")

pr("Monnaie", "Rendre la monnaie", 2,
"""L'algorithme **glouton** du caissier : rendre d'abord le plus possible de la plus grosse pièce,
puis de la suivante, etc. Avec les euros, il rend toujours le minimum de pièces. Mais avec des
pièces de 4, 3 et 1, il se trompe : pour rendre 6, il donne 4 + 1 + 1 au lieu de 3 + 3 !

## À prouver
1. `rendu_somme` : si la dernière pièce vaut 1, le glouton rend exactement la bonne somme.
2. `euros` : pour rendre 3,88 €, le glouton donne une pièce de chaque.
3. `glouton_rate` : avec les pièces 4, 3, 1, le glouton n'est pas optimal.""",
"""def rendu : List Nat → Nat → List Nat
  | [], _ => []
  | p :: ps, n => List.replicate (n / p) p ++ rendu ps (n % p)

theorem rendu_somme (ps : List Nat) (n : Nat) : (rendu (ps ++ [1]) n).sum = n := by -- @exo
  induction ps generalizing n with
  | nil => simp [rendu]
  | cons p ps ih =>
    simp only [List.cons_append, rendu, List.sum_append, List.sum_replicate_nat, ih]
    exact Nat.div_add_mod' n p

theorem euros : rendu [200, 100, 50, 20, 10, 5, 2, 1] 388 = [200, 100, 50, 20, 10, 5, 2, 1] := by -- @exo
  decide

theorem glouton_rate : (rendu [4, 3, 1] 6).length = 3 ∧ [3, 3].sum = 6 ∧ [3, 3].length = 2 := by -- @exo
  decide""",
["Récurrence sur la liste des pièces, en généralisant le montant `n`.", "`List.sum_replicate_nat : (replicate n a).sum = n * a`, et `Nat.div_mul_add_mod : n / p * p + n % p = n`."], "Programmes.Accumulateur",
ressources=["[Problème du rendu de monnaie (Wikipédia)](https://fr.wikipedia.org/wiki/Probl%C3%A8me_du_rendu_de_monnaie)"])

pr("Carrousel", "Le carrousel", 3,
"""`tourner` fait passer le premier élément à la fin : `[1, 2, 3] → [2, 3, 1] → [3, 1, 2] → [1, 2, 3]`.
Après autant de tours que d'éléments, on revient au départ.

## À prouver
1. `tournerN_append : tournerN l₁.length (l₁ ++ l₂) = l₂ ++ l₁`
2. `tour_complet : tournerN l.length l = l`""",
"""def tourner {α : Type} : List α → List α
  | [] => []
  | x :: l => l ++ [x]

def tournerN {α : Type} : Nat → List α → List α
  | 0, l => l
  | n + 1, l => tournerN n (tourner l)

theorem tournerN_append {α : Type} (l₁ l₂ : List α) :
    tournerN l₁.length (l₁ ++ l₂) = l₂ ++ l₁ := by -- @exo
  induction l₁ generalizing l₂ with
  | nil => simp [tournerN]
  | cons x l ih =>
    simp only [List.length_cons, tournerN, List.cons_append, tourner]
    rw [List.append_assoc, ih]
    simp

theorem tour_complet {α : Type} (l : List α) : tournerN l.length l = l := by -- @exo
  simpa using tournerN_append l []""",
["Le bon énoncé à prouver par récurrence est le plus général : `tournerN_append`, sur `l₁`, en généralisant `l₂`.", "`tourner (x :: (l ++ l₂)) = (l ++ l₂) ++ [x] = l ++ (l₂ ++ [x])` (`List.append_assoc`)."], "Programmes.Accumulateur")

pr("Magicien", "Le mélange parfait du magicien", 2,
"""Un magicien coupe un jeu de 52 cartes en deux moitiés égales et les entrelace parfaitement
(carte du dessus, puis une de l'autre moitié, etc.) : c'est le **faro**. Miracle : après **8**
mélanges parfaits, le jeu est revenu dans l'ordre de départ ! Les magiciens s'en servent pour
avoir l'air de mélanger.

## À prouver
1. `longueur_entrelacer`, `longueur_melanger` : on ne perd aucune carte.
2. `magicien` : 8 mélanges ramènent le jeu à l'ordre initial,
3. `pas_avant` : et pas moins de 8.""",
"""def entrelacer {α : Type} : List α → List α → List α
  | x :: xs, y :: ys => x :: y :: entrelacer xs ys
  | xs, [] => xs
  | [], ys => ys

def melanger {α : Type} (l : List α) : List α :=
  entrelacer (l.take (l.length / 2)) (l.drop (l.length / 2))

theorem longueur_entrelacer {α : Type} (xs ys : List α) :
    (entrelacer xs ys).length = xs.length + ys.length := by -- @exo
  induction xs generalizing ys with
  | nil => cases ys <;> simp [entrelacer]
  | cons x xs ih =>
    cases ys with
    | nil => simp [entrelacer]
    | cons y ys =>
      simp only [entrelacer, List.length_cons, ih]
      omega

theorem longueur_melanger {α : Type} (l : List α) : (melanger l).length = l.length := by -- @exo
  simp only [melanger, longueur_entrelacer, List.length_take, List.length_drop]
  omega

theorem magicien : repeter melanger 8 (List.range 52) = List.range 52 := by -- @exo
  decide +kernel

theorem pas_avant : ∀ k, k < 7 → repeter melanger (k + 1) (List.range 52) ≠ List.range 52 := by -- @exo
  decide +kernel""",
["`longueur_entrelacer` : récurrence sur `xs` en généralisant `ys`, puis `cases ys`.", "Les deux derniers sont des calculs : `decide +kernel`."], "Programmes.Carrousel",
ressources=["[Mélange faro (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Faro_shuffle)"])

pr("PairImpair", "Pair et impair, mutuellement", 2,
"""Deux fonctions qui s'appellent l'une l'autre (**récursion mutuelle**) : `n + 1` est pair si `n`
est impair, et impair si `n` est pair.

## À prouver
`pair_impair : estPair n = (n % 2 == 0) ∧ estImpair n = (n % 2 == 1)`

Il faut prouver les deux en même temps : chacune a besoin de l'autre dans la récurrence.""",
"""mutual
def estPair : Nat → Bool
  | 0 => true
  | n + 1 => estImpair n

def estImpair : Nat → Bool
  | 0 => false
  | n + 1 => estPair n
end

theorem pair_impair (n : Nat) : estPair n = (n % 2 == 0) ∧ estImpair n = (n % 2 == 1) := by -- @exo
  induction n with
  | zero => simp [estPair, estImpair]
  | succ n ih =>
    simp only [estPair, estImpair, ih.1, ih.2]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h' : (n + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (n + 1) % 2 = 0 := by omega
      simp [h, h']""",
["Récurrence sur `n` pour la conjonction des deux énoncés.", "Puis deux cas : `n % 2 = 0` ou `1` (`Nat.mod_two_eq_zero_or_one`), et `simp`."], "Programmes.Definitions")

pr("Pascal", "Le triangle de Pascal en listes", 2,
"""Chaque ligne du triangle de Pascal s'obtient en additionnant la ligne précédente décalée et
la ligne précédente : `[1, 3, 3, 1]` → `[0, 1, 3, 3, 1] + [1, 3, 3, 1, 0] = [1, 4, 6, 4, 1]`.
Conséquence : la somme double à chaque ligne, donc la ligne `n` a pour somme `2^n`.

## À prouver
1. `somme_zipWith` : la somme de deux listes additionnées terme à terme.
2. `longueur_pascal : (pascal n).length = n + 1`
3. `somme_pascal : (pascal n).sum = 2 ^ n`
4. `ligne_quatre : pascal 4 = [1, 4, 6, 4, 1]`""",
"""def ligneSuivante (l : List Nat) : List Nat := List.zipWith (· + ·) (0 :: l) (l ++ [0])

def pascal : Nat → List Nat
  | 0 => [1]
  | n + 1 => ligneSuivante (pascal n)

theorem somme_zipWith (a b : List Nat) (h : a.length = b.length) :
    (List.zipWith (· + ·) a b).sum = a.sum + b.sum := by -- @exo
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.zipWith_cons_cons, List.sum_cons, ih b (by simpa using h)]
      omega

theorem longueur_pascal (n : Nat) : (pascal n).length = n + 1 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih => simp [pascal, ligneSuivante, ih]

theorem somme_pascal (n : Nat) : (pascal n).sum = 2 ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pascal, ligneSuivante]
    rw [somme_zipWith _ _ (by simp)]
    simp [ih, Nat.pow_succ]
    omega

theorem ligne_quatre : pascal 4 = [1, 4, 6, 4, 1] := by -- @exo
  decide""",
["`somme_zipWith` : récurrence sur `a` en généralisant `b`, puis `cases b`.", "Pour `somme_pascal` : la somme de `0 :: l` et de `l ++ [0]` vaut deux fois celle de `l`."], "Programmes.Accumulateur",
ressources=["[Triangle de Pascal (Wikipédia)](https://fr.wikipedia.org/wiki/Triangle_de_Pascal)"])

pr("ThueMorse", "Le mot de Thue-Morse", 2,
"""On part de `0`, et à chaque étape on recopie le mot en ajoutant à la suite son « négatif » :
`0 → 01 → 0110 → 01101001 → …`. Ce mot étrange apparaît partout : partage équitable (pour choisir
des équipes, A B B A B A A B est plus juste que A B A B…), échecs (règle de nullité infinie),
fractales…

Une de ses propriétés étonnantes : il ne contient jamais trois fois de suite le même bloc
(« sans cube »).

## À prouver
1. `longueur_thue : (thue n).length = 2 ^ n`
2. `prefixe : thue n <+: thue (n + 1)` (chaque mot prolonge le précédent)
3. `sans_cube` : `thue 5` (32 lettres) ne contient aucun bloc répété trois fois de suite.""",
"""def thue : Nat → List Bool
  | 0 => [false]
  | n + 1 => thue n ++ (thue n).map (!·)

/-- Le mot `w` contient-il un bloc `u` (non vide) suivi de `u` puis encore de `u` ? -/
def aUnCube (w : List Bool) : Bool :=
  (List.range w.length).any fun i => (List.range w.length).any fun k =>
    let u := (w.drop i).take (k + 1)
    i + 3 * (k + 1) ≤ w.length &&
      (w.drop (i + k + 1)).take (k + 1) == u && (w.drop (i + 2 * (k + 1))).take (k + 1) == u

theorem longueur_thue (n : Nat) : (thue n).length = 2 ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [thue, List.length_append, List.length_map, ih, Nat.pow_succ]
    omega

theorem prefixe (n : Nat) : thue n <+: thue (n + 1) := by -- @exo
  exact List.prefix_append _ _

theorem sans_cube : aUnCube (thue 5) = false := by -- @exo
  decide +kernel""",
["`longueur_thue` : récurrence, `List.length_append`, `List.length_map`, `Nat.pow_succ`.", "`prefixe` : `List.prefix_append`.", "`sans_cube` : un calcul, `decide +kernel`."], "Programmes.Pascal",
ressources=["[Suite de Prouhet-Thue-Morse (Wikipédia)](https://fr.wikipedia.org/wiki/Suite_de_Prouhet-Thue-Morse)"])

pr("Kaprekar", "La constante de Kaprekar", 2,
"""Prends un nombre à 3 chiffres (pas tous égaux), range ses chiffres dans l'ordre décroissant
puis croissant, et soustrais : `352 → 532 − 235 = 297 → 972 − 279 = 693 → 963 − 369 = 594 →
954 − 459 = 495 → 954 − 459 = 495`… On tombe **toujours** sur 495 ! (Avec 4 chiffres, c'est
6174 : 7641 − 1467 = 6174.)

Astuce : `grand − petit = 100a + 10b + c − (100c + 10b + a) = 99 × (a − c)` si `a` est le plus
grand chiffre et `c` le plus petit.

## À prouver
1. `kaprekar_495` : pour tout nombre de 0 à 999 dont les chiffres ne sont pas tous égaux,
   6 étapes suffisent pour arriver à 495.
2. `fixe_495 : kaprekar 495 = 495`""",
"""def kaprekar (n : Nat) : Nat :=
  let a := n / 100
  let b := n / 10 % 10
  let c := n % 10
  99 * (max a (max b c) - min a (min b c))

theorem fixe_495 : kaprekar 495 = 495 := by -- @exo
  decide

theorem kaprekar_495 : ∀ n, n < 1000 → (n / 100 ≠ n / 10 % 10 ∨ n / 10 % 10 ≠ n % 10) →
    repeter kaprekar 6 n = 495 := by -- @exo
  decide +kernel""",
["Ce sont des calculs : `decide +kernel` vérifie les 1000 nombres un par un.", "Pour comprendre pourquoi : après une étape, on obtient toujours un multiple de 99 (099, 198, …, 891)."], "Programmes.Magicien",
ressources=["[Algorithme de Kaprekar (Wikipédia)](https://fr.wikipedia.org/wiki/Algorithme_de_Kaprekar)"])

pr("PlusOuMoins", "Le jeu du plus ou moins", 2,
"""« Je pense à un nombre entre 0 et 99. » À chaque essai, on te répond « plus grand » ou « plus
petit ». En visant toujours le **milieu** de l'intervalle restant (dichotomie), **7 essais**
suffisent toujours, car `2^7 = 128 ≥ 100`.

## À prouver
1. `sept_essais` : pour chaque nombre secret, la stratégie le trouve en au plus 7 essais.
2. `parfois_sept` : et il existe un secret qui en demande vraiment 7 (par exemple 0).""",
"""/-- Nombre d'essais pour trouver `s` dans `[lo, hi)` en visant le milieu (`none` si échec). -/
def essais (s : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | f + 1, lo, hi =>
    let m := (lo + hi) / 2
    if s = m then some 1
    else if s < m then (essais s f lo m).map (· + 1)
    else (essais s f (m + 1) hi).map (· + 1)

theorem sept_essais : ∀ s, s < 100 → ∃ k, essais s 10 0 100 = some k ∧ k ≤ 7 := by -- @exo
  intro s hs
  have : ∀ s, s < 100 → ((essais s 10 0 100).getD 100) ≤ 7 ∧ (essais s 10 0 100).isSome := by
    decide +kernel
  obtain ⟨h1, h2⟩ := this s hs
  cases e : essais s 10 0 100 with
  | none => simp [e] at h2
  | some k => exact ⟨k, rfl, by simpa [e] using h1⟩

theorem parfois_sept : essais 0 10 0 100 = some 7 := by -- @exo
  decide""",
["Fais d'abord vérifier à `decide +kernel` un énoncé booléen sur les 100 secrets (avec `Option.getD` et `Option.isSome`).", "Puis `cases e : essais s 10 0 100` pour récupérer le nombre d'essais."], "Programmes.Recherche",
ressources=["[Recherche dichotomique (Wikipédia)](https://fr.wikipedia.org/wiki/Recherche_dichotomique)"])

pr("Crepes", "Le tri des crêpes", 2,
"""Un cuisinier a une pile de crêpes de tailles différentes. Il ne sait faire qu'une chose : glisser
sa spatule sous la `k`-ième crêpe et **retourner** tout le haut de la pile. Peut-il trier la pile ?
Oui : amener la plus grande en haut, puis la retourner tout en bas, et recommencer.
(Bill Gates a publié un article de recherche sur ce problème quand il était étudiant !)

## À prouver
1. `retourner_retourner : retourner k (retourner k l) = l`
2. `longueur_retourner : (retourner k l).length = l.length`
3. `trier_trois : retourner 2 (retourner 3 [3, 1, 2]) = [1, 2, 3]`""",
"""def retourner {α : Type} (k : Nat) (l : List α) : List α := (l.take k).reverse ++ l.drop k

theorem longueur_retourner {α : Type} (k : Nat) (l : List α) :
    (retourner k l).length = l.length := by -- @exo
  simp only [retourner, List.length_append, List.length_reverse, List.length_take, List.length_drop]
  omega

theorem retourner_retourner {α : Type} (k : Nat) (l : List α) :
    retourner k (retourner k l) = l := by -- @exo
  unfold retourner
  by_cases h : k ≤ l.length
  · have hl : ((l.take k).reverse).length = k := by simp; omega
    rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
      List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]
    simp
  · have h1 : l.take k = l := List.take_of_length_le (by omega)
    have h2 : l.drop k = [] := List.drop_of_length_le (by omega)
    rw [h1, h2, List.append_nil, List.take_of_length_le (by simp; omega),
      List.drop_of_length_le (by simp; omega)]
    simp

theorem trier_trois : retourner 2 (retourner 3 [3, 1, 2]) = [1, 2, 3] := by -- @exo
  decide""",
["Sépare les cas `k ≤ l.length` ou non.", "Lemmes utiles : `List.take_append_of_le_length`, `List.drop_append_of_le_length`, `List.take_of_length_le`, `List.drop_of_length_le`."], "Programmes.Carrousel",
ressources=["[Tri de crêpes (Wikipédia)](https://fr.wikipedia.org/wiki/Tri_de_cr%C3%AApes)"])

pr("Luhn", "La clé de Luhn des cartes bancaires", 3,
"""Le dernier chiffre d'un numéro de carte bancaire (ou de SIRET) est une **clé de contrôle** :
la formule de Luhn. En partant de la droite, on double un chiffre sur deux (si le double dépasse
9, on retire 9), on additionne tout, et le total doit être multiple de 10.

À quoi ça sert ? À détecter les **fautes de frappe** : si on se trompe sur un seul chiffre, le
total change forcément modulo 10. C'est ce qu'on va prouver.

Ici, le numéro est donné **à l'envers** (chiffre de droite en tête) ; le booléen dit si le
chiffre courant doit être doublé.

## À prouver
1. `exemple_luhn` : le numéro 79927398713 est valide.
2. `doubler_lt`, `doubler_injectif` : doubler un chiffre donne un chiffre, et deux chiffres
   différents donnent des résultats différents.
3. `luhn_append` : la clé d'une concaténation.
4. `une_faute` : changer un seul chiffre change la clé modulo 10.""",
"""def doubler (d : Nat) : Nat := if 2 * d < 10 then 2 * d else 2 * d - 9

def luhn : List Nat → Bool → Nat
  | [], _ => 0
  | d :: l, b => (if b then doubler d else d) + luhn l (!b)

def valide (numero : List Nat) : Bool := luhn numero.reverse false % 10 == 0

theorem exemple_luhn : valide [7, 9, 9, 2, 7, 3, 9, 8, 7, 1, 3] = true := by -- @exo
  decide

theorem doubler_lt : ∀ a, a < 10 → doubler a < 10 := by -- @exo
  decide

theorem doubler_injectif : ∀ a, a < 10 → ∀ c, c < 10 → doubler a = doubler c → a = c := by -- @exo
  decide

theorem luhn_append (l₁ l₂ : List Nat) (b : Bool) :
    luhn (l₁ ++ l₂) b = luhn l₁ b + luhn l₂ (if l₁.length % 2 = 0 then b else !b) := by -- @exo
  induction l₁ generalizing b with
  | nil => simp [luhn]
  | cons d l ih =>
    simp only [List.cons_append, luhn, ih, List.length_cons]
    rcases Nat.mod_two_eq_zero_or_one l.length with h | h
    · have h' : (l.length + 1) % 2 = 1 := by omega
      simp only [h, h', ↓reduceIte, Nat.one_ne_zero, Nat.add_assoc]
    · have h' : (l.length + 1) % 2 = 0 := by omega
      simp only [h, h', ↓reduceIte, Nat.one_ne_zero, Bool.not_not, Nat.add_assoc]

theorem une_faute (l₁ l₂ : List Nat) (a c : Nat) (b : Bool) (ha : a < 10) (hc : c < 10)
    (h : luhn (l₁ ++ a :: l₂) b % 10 = luhn (l₁ ++ c :: l₂) b % 10) : a = c := by -- @exo
  rw [luhn_append, luhn_append] at h
  simp only [luhn] at h
  have da := doubler_lt a ha
  have dc := doubler_lt c hc
  generalize (if l₁.length % 2 = 0 then b else !b) = b' at h
  cases b'
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    omega
  · simp only [↓reduceIte] at h
    exact doubler_injectif a ha c hc (by omega)""",
["`doubler_lt` et `doubler_injectif` : seulement 10 chiffres à essayer, `decide`.", "`luhn_append` : récurrence sur `l₁` en généralisant `b` ; deux cas selon la parité de la longueur.", "`une_faute` : décompose avec `luhn_append`, puis le chiffre modifié a la même contribution modulo 10 ; si elle est doublée, utilise `doubler_injectif`."], "Programmes.Onze",
ressources=["[Formule de Luhn (Wikipédia)](https://fr.wikipedia.org/wiki/Formule_de_Luhn)"])

# --- Circuits : compteur binaire et code de Gray
C = "Solutions.Circuits.Definitions"
exo("Circuits", "Increment", "Le compteur binaire", 2, [C],
"""Ajouter 1 en binaire : on parcourt les bits depuis le poids faible ; les `1` deviennent des `0`
(c'est la retenue qui se propage) jusqu'au premier `0`, qui devient `1`.
`[true, true, false, true]` (= 11) devient `[false, false, true, true]` (= 12).

## À prouver
1. `incr_valeur : valeur (incr l) = valeur l + 1`
2. `incr_longueur` : la longueur augmente d'au plus 1.""",
"""def incr : List Bool → List Bool
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: incr l

theorem incr_valeur (l : List Bool) : valeur (incr l) = valeur l + 1 := by -- @exo
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b
    · simp [incr, valeur_cons]
      omega
    · simp [incr, valeur_cons, ih]
      omega

theorem incr_longueur (l : List Bool) : (incr l).length ≤ l.length + 1 := by -- @exo
  induction l with
  | nil => simp [incr]
  | cons b l ih =>
    cases b
    · simp [incr]
    · simp [incr]
      omega""",
["Récurrence sur `l`, puis `cases b` sur le premier bit.", "`valeur_cons : valeur (b :: l) = b.toNat + 2 * valeur l`."], "Parcours.Circuits", requiert="Circuits.VersBinaire")

exo("Circuits", "Gray", "Le code de Gray", 2, [C],
"""Dans un compteur ordinaire, passer de 0111 à 1000 change 4 bits à la fois : si les bits ne
changent pas exactement au même instant, on lit n'importe quoi. Le **code de Gray** énumère tous
les mots de `n` bits de façon que deux mots consécutifs ne diffèrent que d'**un seul** bit.
(Utilisé dans les capteurs de position, les roues codeuses, les tableaux de Karnaugh…)

Construction « miroir » : on écrit la liste pour `n` bits précédée de `0`, puis la même liste
**à l'envers** précédée de `1`.

## À prouver
1. `longueur_gray : (gray n).length = 2 ^ n`
2. `mots_gray : w ∈ gray n → w.length = n`
3. `gray_quatre` : dans `gray 4`, deux mots consécutifs diffèrent d'exactement un bit.""",
"""def gray : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (gray n).map (false :: ·) ++ (gray n).reverse.map (true :: ·)

/-- Nombre de positions où deux mots diffèrent. -/
def ecarts (u v : List Bool) : Nat := ((List.zipWith (· != ·) u v).filter id).length

def voisins : List (List Bool) → Bool
  | u :: v :: l => ecarts u v == 1 && voisins (v :: l)
  | _ => true

theorem longueur_gray (n : Nat) : (gray n).length = 2 ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [gray, List.length_append, List.length_map, List.length_reverse, ih, Nat.pow_succ]
    omega

theorem mots_gray (n : Nat) : ∀ w ∈ gray n, w.length = n := by -- @exo
  induction n with
  | zero => simp [gray]
  | succ n ih =>
    simp only [gray, List.mem_append, List.mem_map, List.mem_reverse]
    rintro w (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) <;> simp [ih a ha]

theorem gray_quatre : voisins (gray 4) = true := by -- @exo
  decide""",
["`longueur_gray` : récurrence ; `List.length_append`, `List.length_map`, `List.length_reverse`.", "`mots_gray` : un mot de `gray (n + 1)` est `false :: a` ou `true :: a` avec `a ∈ gray n` (`List.mem_map`)."], "Parcours.Circuits", requiert="Circuits.Increment",
ressources=["[Code de Gray (Wikipédia)](https://fr.wikipedia.org/wiki/Code_de_Gray)"])

ecrire_tout()
