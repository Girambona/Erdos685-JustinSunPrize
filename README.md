# Erdős #686, cas k = 2 (exercice en Lean)

Problème de référence : Erdős #686 (https://www.erdosproblems.com/686), **ouvert**.
Ce dépôt ne le résout pas.

## Contenu
`Erdos686_k2.lean` :
- la définition P(k,m) = (m+1)…(m+k) ;
- pour k = 2, N = 4, 9, 25, 49 ne sont pas représentables : P(2,m) ≠ N·P(2,n) ;
- des exemples représentables avec m ≥ n+2 : N = 2, 3, 36, 1225 ;
- l'énoncé trivial sans la condition m ≥ n+k (ce n'est pas le problème 686).

## Limites
Ces cas particuliers sont très probablement déjà connus (fil du problème 686 :
Tao pour N = 4, classification de natso26 pour k = 2, 9 mars 2026). Je ne
revendique rien de nouveau. Le fichier compile sans erreur dans Lean Web
(Mathlib), mais n'a pas été relu par un tiers.

## Historique
Une première version affirmait à tort avoir résolu « Erdős 685 ». C'était faux :
mauvais numéro de problème, et la construction ne respectait pas m ≥ n+k.
Les issues correspondantes sont retirées.

## Transparence
Travail fait avec l'aide d'outils d'IA (Meta AI, Claude).
