import ParcoursOutils

/-!
# Les sorites de Lewis Carroll

Lewis Carroll (l'auteur d'*Alice au pays des merveilles*) était aussi logicien. Il inventait des
« sorites » : des chaînes de prémisses absurdes dont il fallait tirer la conclusion.

**Les bébés.** (1) Les bébés sont illogiques. (2) Personne n'est méprisé s'il sait dompter un
crocodile. (3) Les gens illogiques sont méprisés. Conclusion : les bébés ne savent pas dompter les
crocodiles.

**Les canards.** (1) Aucun canard ne danse la valse. (2) Aucun officier ne refuse de danser la
valse. (3) Toutes mes volailles sont des canards. Conclusion : mes volailles ne sont pas
officiers.

## À prouver
`bebes` et `canards`.

## Ressources
- [Lewis Carroll, *Symbolic Logic* (Wikipédia, en anglais)](https://en.wikipedia.org/wiki/Symbolic_Logic_(book))

---
*Exercice* `Logique.Carroll` · difficulté ★☆☆☆☆

💡 Indices : `./parcours indice Logique.Carroll` · ✅ Vérification : regarde le message de `#verifier` tout en bas du fichier (dans l'infoview), ou lance `./parcours verifier`.
-/

namespace Parcours.Logique

theorem bebes {Gens : Type} (Bebe Logique Meprise Dompteur : Gens → Prop)
    (h1 : ∀ x, Bebe x → ¬Logique x) (h2 : ∀ x, Dompteur x → ¬Meprise x)
    (h3 : ∀ x, ¬Logique x → Meprise x) : ∀ x, Bebe x → ¬Dompteur x := by
  sorry

theorem canards {Etre : Type} (Canard Valse Officier Volaille : Etre → Prop)
    (h1 : ∀ x, Canard x → ¬Valse x) (h2 : ∀ x, Officier x → Valse x)
    (h3 : ∀ x, Volaille x → Canard x) : ∀ x, Volaille x → ¬Officier x := by
  sorry

end Parcours.Logique

#verifier
