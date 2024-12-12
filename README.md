# Projet d'assistant de preuves du cours CSC_51051_EP

Il s'agit d'un fork du template pour le [projet d'assistant de preuves du cours CSC_51051_EP](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/4.prover.html). Il comporte 3 grand répertoires :

1. [simple](simple/): l'assistant de preuves pour la logique propositionnelle (parties 1 à 4).
2. [dependent](dependent/): l'assistant de preuves avec des types dépendants (partie 5).
3. [report](report/): le rapport avec la source Markdown.

Pour compiler le projet, il suffit de faire ```make``` à la racine afin de construire l'assistant de preuves pour les types simples et les types dépendants. De plus, on peut faire ```make tests``` pour lancer les tests unitaires, ```make proofs``` pour lancer les preuves et ```make exec``` pour seulement lancer le prouveur.
