import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fabrique import exo, ecrire_tout

RD = "Solutions.Recurrence.Definitions"
AD = "Solutions.Arithmetique.Definitions"
NS = "Parcours.Classiques"
OPEN = "open Parcours.Recurrence\n\n"

def cl(ident, titre, diff, imports, image, enonce, code, indices, requiert="", ressources=(), celebre=0):
    texte = "## Se le représenter\n" + image.strip() + "\n\n## À prouver\n" + enonce.strip()
    exo("Classiques", ident, titre, diff, imports, texte, OPEN + code.strip(), indices, NS,
        requiert=requiert, ressources=ressources, celebre=celebre)

cl("SommePairs", "La somme des nombres pairs", 1, [RD],
 """Empile les nombres pairs `0, 2, 4, …, 2(n−1)` en colonnes de points : tu obtiens un rectangle
`n × (n − 1)` (deux escaliers identiques collés). Donc la somme vaut `n(n − 1)`.""",
 "`somme_pairs (n : Nat) : somme (fun i => 2 * i) n + n = n * n` (c'est-à-dire `n(n − 1)`, sans soustraction)",
 """theorem somme_pairs (n : Nat) : somme (fun i => 2 * i) n + n = n * n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ]
    grind""",
 ["Récurrence, `somme_succ`, puis `grind` (avec l'hypothèse de récurrence dans le contexte)."], requiert="Recurrence.Impairs")
cl("Triangulaires", "Deux triangles font un carré", 2, [RD, "Solutions.Recurrence.Gauss"],
 """Le nombre triangulaire `T(n) = 0 + 1 + ⋯ + n` compte les points d'un triangle (les quilles au bowling :
`T(4) = 10`). Colle un triangle de côté `n` et un triangle de côté `n + 1` le long de la diagonale :
ils forment un **carré** `(n + 1) × (n + 1)`.""",
 "`deux_triangles (n : Nat) : tri n + tri (n + 1) = (n + 1) ^ 2` où `tri n = somme (fun i => i) (n + 1)`",
 """def tri (n : Nat) : Nat := somme (fun i => i) (n + 1)

theorem deux_triangles (n : Nat) : tri n + tri (n + 1) = (n + 1) ^ 2 := by -- @exo
  have g := gauss n
  unfold tri
  rw [somme_succ (fun i => i) (n + 1)]
  grind""",
 ["`tri (n + 1) = tri n + (n + 1)` (`somme_succ`).", "Avec la somme de Gauss (`gauss n : 2 * tri n = n * (n + 1)`), c'est un calcul : `grind`."], requiert="Recurrence.Gauss")
cl("HuitTriangles", "Huit triangles et un point", 2, [RD, "Solutions.Recurrence.Gauss"],
 """Prends 8 copies d'un triangle de côté `n` et un point : en les assemblant autour du point central,
on obtient un carré de côté `2n + 1`. (Diophante l'avait remarqué ; c'est un test pour savoir si un
nombre est triangulaire.)""",
 "`huit_triangles (n : Nat) : 8 * somme (fun i => i) (n + 1) + 1 = (2 * n + 1) ^ 2`",
 """theorem huit_triangles (n : Nat) : 8 * somme (fun i => i) (n + 1) + 1 = (2 * n + 1) ^ 2 := by -- @exo
  have g := gauss n
  grind""",
 ["Utilise `gauss n` puis `grind`."], requiert="Classiques.Triangulaires")
cl("Telescopique", "Une somme télescopique", 2, [RD],
 """`(1² − 0²) + (2² − 1²) + (3² − 2²) + ⋯` : chaque terme annule une partie du précédent, comme un
télescope qu'on replie. Il ne reste que le dernier carré.""",
 "`telescopique (n : Nat) : somme (fun i => (i + 1) ^ 2 - i ^ 2) n = n ^ 2`",
 """theorem telescopique (n : Nat) : somme (fun i => (i + 1) ^ 2 - i ^ 2) n = n ^ 2 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, ih]
    have h : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega""",
 ["Récurrence. Dans le cas `succ`, il faut savoir que `n² ≤ (n+1)²` pour que la soustraction se passe bien (`Nat.pow_le_pow_left`).", "Puis `omega`."], requiert="Recurrence.Impairs")
cl("ProduitsConsecutifs", "La somme des produits consécutifs", 2, [RD],
 """`1·2 + 2·3 + 3·4 + ⋯ + n(n+1) = n(n+1)(n+2)/3`. Visuellement : des « boîtes » `i × (i+1)` qui
s'empilent en une pyramide dont le volume est un tiers d'un pavé.""",
 "`produits_consecutifs (n : Nat) : 3 * somme (fun i => i * (i + 1)) (n + 1) = n * (n + 1) * (n + 2)`",
 """theorem produits_consecutifs (n : Nat) :
    3 * somme (fun i => i * (i + 1)) (n + 1) = n * (n + 1) * (n + 2) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, Nat.mul_add, ih]
    grind""",
 ["Récurrence ; `somme_succ`, `Nat.mul_add`, l'hypothèse de récurrence, puis `grind`."], requiert="Recurrence.Carres")
cl("CarresImpairs", "La somme des carrés impairs", 2, [RD],
 """`1² + 3² + 5² + ⋯ + (2n−1)² = n(2n−1)(2n+1)/3`. Sans division ni soustraction :
`3 × somme + n = 4n³`.""",
 "`carres_impairs (n : Nat) : 3 * somme (fun i => (2 * i + 1) ^ 2) n + n = 4 * n ^ 3`",
 """theorem carres_impairs (n : Nat) : 3 * somme (fun i => (2 * i + 1) ^ 2) n + n = 4 * n ^ 3 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, Nat.mul_add]
    grind""",
 ["Récurrence ; `somme_succ`, `Nat.mul_add`, puis `grind`."], requiert="Recurrence.Carres")
cl("Pentagonaux", "Les nombres pentagonaux", 2, [RD],
 """`1, 5, 12, 22, 35, …` : les points de pentagones emboîtés. On passe d'un pentagone au suivant en
ajoutant trois côtés de `n + 1` points, moins les deux coins partagés : `3n + 1` points.
Formule : `P(n) = n(3n − 1)/2`.""",
 "`pentagonaux (n : Nat) : 2 * pent n + n = 3 * n ^ 2`",
 """def pent : Nat → Nat
  | 0 => 0
  | n + 1 => pent n + 3 * n + 1

theorem pentagonaux (n : Nat) : 2 * pent n + n = 3 * n ^ 2 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pent]
    grind""",
 ["Récurrence ; déplie `pent` (`simp only [pent]`), puis `grind`."], requiert="Classiques.Triangulaires")
cl("FibSomme", "La somme des Fibonacci", 2, [RD],
 """`0 + 1 + 1 + 2 + 3 + 5 + 8 = 20 = 21 − 1`. La somme des premiers Fibonacci est un Fibonacci moins 1 :
chaque nouveau terme « absorbe » les précédents.""",
 "`fib_somme (n : Nat) : somme fib n + 1 = fib (n + 1)`",
 """theorem fib_somme (n : Nat) : somme fib n + 1 = fib (n + 1) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, show n + 1 + 1 = n + 2 from rfl, fib_add_two]
    omega""",
 ["Récurrence ; `somme_succ` et `fib_add_two`, puis `omega`."], requiert="Recurrence.Fibonacci")
cl("FibCarres", "Le rectangle d'or des Fibonacci", 3, [RD],
 """Dessine des carrés de côtés `1, 1, 2, 3, 5, 8, …` en spirale : ils remplissent exactement un rectangle
de côtés `F(n)` et `F(n+1)`. Donc la somme des carrés des Fibonacci est `F(n)·F(n+1)`.
(C'est la figure de la « spirale d'or ».)""",
 "`fib_carres (n : Nat) : somme (fun i => fib i ^ 2) (n + 1) = fib n * fib (n + 1)`",
 """theorem fib_carres (n : Nat) : somme (fun i => fib i ^ 2) (n + 1) = fib n * fib (n + 1) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, ih, show n + 1 + 1 = n + 2 from rfl, fib_add_two]
    grind""",
 ["Récurrence ; `somme_succ`, `ih`, puis `fib_add_two` et `grind`."], requiert="Classiques.FibSomme")
cl("FibImpairs", "Les Fibonacci d'indice impair", 3, [RD],
 """`F(1) + F(3) + F(5) = 1 + 2 + 5 = 8 = F(6)`. Chaque terme d'indice pair est la somme du terme
précédent (pair) et d'un terme impair : en déroulant, les impairs s'additionnent.""",
 "`fib_impairs (n : Nat) : somme (fun i => fib (2 * i + 1)) n = fib (2 * n)`",
 """theorem fib_impairs (n : Nat) : somme (fun i => fib (2 * i + 1)) n = fib (2 * n) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, ih, show 2 * (n + 1) = 2 * n + 2 by omega, fib_add_two]""",
 ["Récurrence ; `2 * (n + 1) = 2 * n + 2`, puis `fib_add_two`."], requiert="Classiques.FibSomme")
cl("PuissancesTrois", "Les puissances de 3", 2, [RD],
 """`1 + 3 + 9 + 27 = 40` et `2 × 40 + 1 = 81 = 3⁴`. Tout comme `1 + 2 + 4 + ⋯ = 2ⁿ − 1` en binaire,
en base 3 : `222…2` (n chiffres) plus 1 donne `1000…0`.""",
 "`puissances_trois (n : Nat) : 2 * somme (fun i => 3 ^ i) n + 1 = 3 ^ n`",
 """theorem puissances_trois (n : Nat) : 2 * somme (fun i => 3 ^ i) n + 1 = 3 ^ n := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [somme_succ, Nat.pow_succ]
    omega""",
 ["Récurrence ; `somme_succ`, `Nat.pow_succ`, puis `omega`."], requiert="Recurrence.Geometrique")
cl("DeuxN", "Doubler bat ajouter", 1, [RD],
 """Doubler à chaque étape (`2ⁿ`) va toujours au moins aussi vite qu'ajouter 2 à chaque étape (`2n`).""",
 "`deux_n (n : Nat) : 2 * n ≤ 2 ^ n`",
 """theorem deux_n (n : Nat) : 2 * n ≤ 2 ^ n := by -- @exo
  induction n with
  | zero => decide
  | succ n ih =>
    have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.pow_succ]
    omega""",
 ["Récurrence ; `Nat.pow_succ`, et `2 ^ n ≥ 1` (`Nat.one_le_two_pow`), puis `omega`."], requiert="Recurrence.Croissance")
cl("FactCarre", "La factorielle bat le carré", 3, [RD],
 """`4! = 24 ≥ 16 = 4²`, `5! = 120 ≥ 25`… et ensuite chaque étape multiplie la factorielle par `n + 1`,
alors que le carré grandit beaucoup moins.""",
 "`fact_carre (n : Nat) (h : 4 ≤ n) : n ^ 2 ≤ fact n`",
 """theorem fact_carre (n : Nat) (h : 4 ≤ n) : n ^ 2 ≤ fact n := by -- @exo
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  clear h
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show k + 1 + 4 = (k + 4) + 1 by omega, fact_succ]
    have h1 : (k + 4 + 1) * (k + 4) ^ 2 ≤ (k + 4 + 1) * fact (k + 4) := Nat.mul_le_mul_left _ ih
    have h2 : k + 4 + 1 ≤ (k + 4) ^ 2 := by grind
    have h3 : (k + 4 + 1) * (k + 4 + 1) ≤ (k + 4 + 1) * (k + 4) ^ 2 := Nat.mul_le_mul_left _ h2
    rw [Nat.pow_two]
    omega""",
 ["Écris `n = k + 4` et fais une récurrence sur `k`.", "`(n+1)! = (n+1)·n! ≥ (n+1)·n² ≥ (n+1)·(n+1)` car `n² ≥ n + 1`. `Nat.mul_le_mul_left` pour multiplier des inégalités."], requiert="Recurrence.Croissance")
cl("Divisible3", "n³ + 2n est divisible par 3", 2, [AD],
 """`n³ + 2n = n³ − n + 3n = (n−1)n(n+1) + 3n` : trois entiers consécutifs contiennent toujours un multiple
de 3. En Lean, on raisonne directement sur le reste de `n` modulo 3.""",
 "`divisible_trois (n : Nat) : (n * n * n + 2 * n) % 3 = 0`",
 """theorem divisible_trois (n : Nat) : (n * n * n + 2 * n) % 3 = 0 := by -- @exo
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h | h | h <;> simp [Nat.add_mod, Nat.mul_mod, h]""",
 ["Trois cas sur `n % 3`, puis `simp [Nat.add_mod, Nat.mul_mod, h]`."], requiert="Olympiades.Parite")
cl("TroisConsecutifs", "Trois entiers consécutifs", 2, [AD],
 """Parmi trois entiers consécutifs, il y a un multiple de 2 et un multiple de 3 : leur produit est
divisible par 6.""",
 "`trois_consecutifs (n : Nat) : (n * (n + 1) * (n + 2)) % 6 = 0`",
 """theorem trois_consecutifs (n : Nat) : (n * (n + 1) * (n + 2)) % 6 = 0 := by -- @exo
  have : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases this with h | h | h | h | h | h <;> simp [Nat.add_mod, Nat.mul_mod, h]""",
 ["Six cas sur `n % 6`."], requiert="Classiques.Divisible3")
cl("Seize", "Les puissances de 16 et le chiffre 5", 2, [AD],
 """`16 = 15 + 1`, donc toutes les puissances de 16 valent 1 modulo 5 (et se terminent par 6 en base 10 !).""",
 "`seize (n : Nat) : (16 ^ n) % 5 = 1`",
 """theorem seize (n : Nat) : (16 ^ n) % 5 = 1 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]""",
 ["Récurrence ; `Nat.pow_succ`, `Nat.mul_mod`, `ih`."], requiert="Olympiades.Sept")
cl("NeufEtDix", "Pourquoi la preuve par neuf marche", 2, [AD],
 """`10 = 9 + 1` : toutes les puissances de 10 valent 1 modulo 9. Donc `abc = 100a + 10b + c ≡ a + b + c`.
C'est le secret de la preuve par neuf.""",
 "`dix_mod_neuf (n : Nat) : (10 ^ n) % 9 = 1`",
 """theorem dix_mod_neuf (n : Nat) : (10 ^ n) % 9 = 1 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, Nat.mul_mod, ih]""",
 ["Récurrence ; `Nat.pow_succ`, `Nat.mul_mod`, `ih`."], requiert="Classiques.Seize")
cl("ImpairCarre8", "Le carré d'un impair modulo 8", 2, [AD],
 """`1, 9, 25, 49, 81, …` : tous les carrés impairs valent 1 modulo 8. Car `(2n+1)² = 4n(n+1) + 1`,
et `n(n+1)` est pair.""",
 "`impair_carre (n : Nat) : ((2 * n + 1) ^ 2) % 8 = 1`",
 """theorem impair_carre (n : Nat) : ((2 * n + 1) ^ 2) % 8 = 1 := by -- @exo
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    have e : (2 * (2 * k) + 1) ^ 2 = 16 * (k * k) + 8 * k + 1 := by grind
    rw [e]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    have e : (2 * (2 * k + 1) + 1) ^ 2 = 16 * (k * k) + 24 * k + 9 := by grind
    rw [e]
    omega""",
 ["Sépare `n` pair (`n = 2k`) et impair (`n = 2k + 1`).", "Développe avec `grind` (`(4k+1)² = 16k² + 8k + 1`), puis `omega`."], requiert="Classiques.Divisible3")
cl("CarrePair", "Un carré est pair ssi…", 1, [AD],
 """Si `n` est impair, `n × n` aussi (impair × impair = impair). C'est l'argument clé de l'irrationalité de √2.""",
 "`carre_pair (n : Nat) : (n * n) % 2 = 0 ↔ n % 2 = 0`",
 """theorem carre_pair (n : Nat) : (n * n) % 2 = 0 ↔ n % 2 = 0 := by -- @exo
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [Nat.mul_mod, h]""",
 ["Deux cas sur `n % 2` ; `simp [Nat.mul_mod, h]`."], requiert="Olympiades.Parite")
cl("TroisChaussettes", "Trois chaussettes", 1, [AD],
 """Dans un tiroir de chaussettes noires et blanches, il suffit d'en prendre **trois** pour avoir une paire
de la même couleur. Version nombres : parmi trois entiers, deux ont la même parité.""",
 "`trois_chaussettes (a b c : Nat) : a % 2 = b % 2 ∨ b % 2 = c % 2 ∨ a % 2 = c % 2`",
 """theorem trois_chaussettes (a b c : Nat) : a % 2 = b % 2 ∨ b % 2 = c % 2 ∨ a % 2 = c % 2 := by -- @exo
  omega""",
 ["`omega` sait raisonner par cas tout seul."], requiert="Combinatoire.Tiroirs")
cl("Diagonales", "Les diagonales d'un polygone", 2, [AD],
 """Un carré a 2 diagonales, un pentagone 5, un hexagone 9. Quand on ajoute un sommet à un polygone à `n`
côtés, le nouveau sommet se relie à `n − 2` sommets non voisins, et l'ancien côté devient une diagonale :
`n − 1` diagonales de plus. Formule : `n(n − 3)/2`.

Ici, `diag k` est le nombre de diagonales d'un polygone à `k + 3` côtés.""",
 "`diagonales (k : Nat) : 2 * diag k = (k + 3) * k`",
 """def diag : Nat → Nat
  | 0 => 0
  | k + 1 => diag k + (k + 2)

theorem diagonales (k : Nat) : 2 * diag k = (k + 3) * k := by -- @exo
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [diag]
    grind""",
 ["Récurrence ; `simp only [diag]`, puis `grind`."], requiert="Combinatoire.DeuxParmi")
cl("Pizza", "Découper une pizza", 2, [RD],
 """Avec `n` coupes droites (sans passer par le même point), combien de morceaux au maximum ? La `n`-ième
coupe croise les `n − 1` précédentes, et traverse donc `n` morceaux, qu'elle coupe chacun en deux :
`n` morceaux de plus. (Le « problème du traiteur paresseux ».) Formule : `(n² + n + 2)/2`.""",
 "`pizza (n : Nat) : 2 * morceaux n = n * n + n + 2`",
 """def morceaux : Nat → Nat
  | 0 => 1
  | n + 1 => morceaux n + (n + 1)

theorem pizza (n : Nat) : 2 * morceaux n = n * n + n + 2 := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [morceaux]
    grind""",
 ["Récurrence ; `simp only [morceaux]`, puis `grind`."], requiert="Classiques.Triangulaires",
 ressources=["[Suite du traiteur paresseux (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Lazy_caterer%27s_sequence)"])
cl("CarresGrille", "Combien de carrés sur un échiquier ?", 3, [RD],
 """Sur un échiquier `n × n`, combien de carrés de toutes tailles ? Pour la taille `k`, il y en a
`(n − k + 1)²`. Au total : `1² + 2² + ⋯ + n²`. Pour un échiquier 8 × 8 : 204 carrés ! On définit
`carres (n + 1) = carres n + (n + 1)²` (agrandir la grille d'un rang ajoute `(n+1)²` carrés).""",
 "`carres_grille (n : Nat) : 6 * carres n = n * (n + 1) * (2 * n + 1)`, et `carres 8 = 204`",
 """def carres : Nat → Nat
  | 0 => 0
  | n + 1 => carres n + (n + 1) ^ 2

theorem carres_grille (n : Nat) : 6 * carres n = n * (n + 1) * (2 * n + 1) := by -- @exo
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [carres]
    grind

theorem echiquier : carres 8 = 204 := by -- @exo
  decide""",
 ["Récurrence ; `simp only [carres]`, puis `grind`.", "Pour l'échiquier : `decide`."], requiert="Recurrence.Carres")
cl("Moyenne", "La moyenne est entre les deux", 1, [RD],
 """La moyenne de deux nombres est entre les deux (ici avec la division entière).""",
 "`moyenne : a ≤ b → a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b`, et `max_min : max a b + min a b = a + b`",
 """theorem moyenne (a b : Nat) (h : a ≤ b) : a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b := by -- @exo
  omega

theorem max_min (a b : Nat) : max a b + min a b = a + b := by -- @exo
  omega""",
 ["`omega` connaît `/ 2`, `max` et `min`."], requiert="Gymnase.Omega")
cl("Pythagore", "Fabriquer des triangles rectangles", 2, [AD],
 """`3² + 4² = 5²`, `5² + 12² = 13²`, `8² + 15² = 17²`… Euclide a trouvé une machine à fabriquer des
triplets de Pythagore : pour tous `m > n`, `(m² − n², 2mn, m² + n²)` en est un.""",
 "`euclide_pythagore (m n : Int) : (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2`, et `trois_quatre_cinq`",
 """theorem euclide_pythagore (m n : Int) :
    (m ^ 2 - n ^ 2) ^ 2 + (2 * m * n) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by -- @exo
  grind

theorem trois_quatre_cinq : (3 : Nat) ^ 2 + 4 ^ 2 = 5 ^ 2 := by -- @exo
  decide""",
 ["`grind` développe et compare.", "Essaie `m = 2, n = 1` : tu retrouves `(3, 4, 5)`."], requiert="Olympiades.QuatreConsecutifs",
 ressources=["[Triplet pythagoricien (Wikipédia)](https://fr.wikipedia.org/wiki/Triplet_pythagoricien)"])
cl("SophieGermain", "L'identité de Sophie Germain", 2, [AD],
 """`n⁴ + 4 = (n² + 2n + 2)(n² − 2n + 2)`. Astuce : `n⁴ + 4 = (n² + 2)² − (2n)²`, une différence de
carrés ! Conséquence : `n⁴ + 4` n'est jamais premier pour `n > 1`. (Sophie Germain, mathématicienne
française autodidacte, 1776–1831.)""",
 "`sophie_germain (n : Int) : n ^ 4 + 4 = (n ^ 2 + 2 * n + 2) * (n ^ 2 - 2 * n + 2)`",
 """theorem sophie_germain (n : Int) : n ^ 4 + 4 = (n ^ 2 + 2 * n + 2) * (n ^ 2 - 2 * n + 2) := by -- @exo
  grind""",
 ["`grind`. Mais essaie de voir la différence de carrés avant !"], requiert="Classiques.Pythagore",
 ressources=["[Sophie Germain (Wikipédia)](https://fr.wikipedia.org/wiki/Sophie_Germain)"])
cl("CauchySchwarz", "L'inégalité de Cauchy-Schwarz", 3, [AD],
 """Pour deux vecteurs `(a, b)` et `(c, d)` du plan, le produit scalaire est plus petit que le produit des
longueurs : `(ac + bd)² ≤ (a² + b²)(c² + d²)`. L'identité de Lagrange explique tout :
la différence vaut exactement `(ad − bc)²`, un carré, donc positive.""",
 "`carre_positif (x : Int) : 0 ≤ x * x`, puis `cauchy_schwarz (a b c d : Int) : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)`",
 """theorem carre_positif (x : Int) : 0 ≤ x * x := by -- @exo
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have := Int.mul_nonneg (Int.neg_nonneg_of_nonpos h) (Int.neg_nonneg_of_nonpos h)
    rwa [Int.neg_mul_neg] at this

theorem cauchy_schwarz (a b c d : Int) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by -- @exo
  have h := carre_positif (a * d - b * c)
  grind""",
 ["Un carré est positif : sépare `x ≥ 0` et `x ≤ 0` (`Int.le_total`), puis `Int.mul_nonneg`. Pour `x ≤ 0`, passe par `-x` (`Int.neg_mul_neg`).", "Pour Cauchy-Schwarz : `carre_positif (a * d - b * c)`, puis `grind` trouve la combinaison."], requiert="Olympiades.AMGM", celebre=78,
 ressources=["[Inégalité de Cauchy-Schwarz (Wikipédia)](https://fr.wikipedia.org/wiki/In%C3%A9galit%C3%A9_de_Cauchy-Schwarz)"])
cl("Racine3", "√3 est irrationnel", 2, ["Solutions.Arithmetique.RacinePremier", "Solutions.Arithmetique.TestPrimalite"],
 """Tu as prouvé que `√p` est irrationnel pour tout premier `p`, et tu as un test de primalité.
Assemble les deux !""",
 "`racine_trois : ¬∃ a b : Nat, 0 < b ∧ a * a = 3 * (b * b)`",
 """open Parcours.Arith

theorem racine_trois : ¬∃ a b : Nat, 0 < b ∧ a * a = 3 * (b * b) := by -- @exo
  exact racine_premier_irrationnelle ((estPremier_correct 3).mp (by decide))""",
 ["`racine_premier_irrationnelle` attend une preuve de `Premier 3`.", "`(estPremier_correct 3).mp (by decide)` en fournit une."], requiert="Arithmetique.TestPrimalite")

ecrire_tout()
