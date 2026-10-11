# Da dove viene la regola di Born

Nota della tappa M5 di `plans/roadmap.md`. Dice dove sta la regola di Born nel nucleo, che cosa i teoremi noti ne derivano, e che cosa costerebbe derivarla qui. I nomi in corpo di testo sono lemmi di Lean 4.34.1.

## Dove sta

Nel nucleo il peso di un esito è il modulo quadro di un'ampiezza: `columnBorn`, `bornPair`, `bornOct`. È una definizione. `projector_born` dice che coincide con `⟨ψ|Π₀|ψ⟩`. `pointer_born` sposta la definizione dal sistema all'apparato, ma non la deriva: il peso dell'apparato è ancora un modulo quadro.

Ciò che i teoremi mostrano è la coerenza della scelta. I pesi sommano a `1` (`ground_prob_sum`), non cambiano sotto `Φ` (`literal_evolution_norm`), non cambiano sotto un cambio di base (`conj_born`), e un apparato lontano non li sposta (`no_signalling_any_0`).

## Che cosa si deriva altrove

**Gleason (1957).** Su uno spazio di Hilbert di dimensione almeno 3, ogni misura di probabilità sui sottospazi chiusi, additiva sulle famiglie di sottospazi ortogonali, è data da un operatore densità con la regola della traccia. In dimensione 2 il teorema è falso: un solo qubit ammette assegnazioni non quadratiche.

**Busch (2003).** Se la probabilità è definita sugli effetti, cioè sulle misure POVM, e non solo sui proiettori, la stessa conclusione vale anche in dimensione 2, con una prova breve. Caves, Fuchs, Manne e Renes (2004) danno una prova elementare sulle POVM che copre anche il qubit e gli spazi vettoriali su campi razionali, dove il teorema originale fallisce.

**Zurek (2003).** L'«envariance»: in uno stato entangled con l'ambiente, una simmetria che scambia i rami dà pesi uguali ai rami di ampiezza uguale. Da lì la regola del modulo quadro. L'argomento presuppone la struttura del prodotto tensoriale e una nozione di indipendenza dall'ambiente.

**Deutsch (1999), Wallace (2012).** Nell'interpretazione a molti mondi, un agente razionale che rispetta alcune regole di decisione deve pesare i rami con il modulo quadro.

## Che cosa costerebbe qui

Il teorema di Gleason chiede l'analisi su uno spazio di dimensione almeno 3 e una misura su tutti i sottospazi. Senza Mathlib è fuori portata. La versione di Busch è algebrica: lineare negli effetti, normalizzata, positiva. La sua prova ricava la linearità sui coefficienti razionali e la estende ai reali per continuità, e nel nucleo la continuità non c'è. La versione di Caves, Fuchs, Manne e Renes sugli spazi su campi razionali non ha bisogno di quel passo: è la più vicina a un nucleo i cui coefficienti sono razionali di Gauss.

Una versione che si può enunciare qui: ogni funzione additiva sugli effetti diagonali di un qubit, con coefficienti razionali, normalizzata a `1`, è il modulo quadro sui due vettori di base. È un teorema di algebra lineare su `ℚ`, alla portata di Lean. Non sarebbe la regola di Born derivata, ma la sua unicità in un caso finito. È un candidato per dopo la 1.0, non un criterio della roadmap.

## Fonti

- A. M. Gleason, «Measures on the closed subspaces of a Hilbert space», _J. Math. Mech._ 6, 885 (1957).
- P. Busch, «Quantum states and generalized observables: a simple proof of Gleason's theorem», _Phys. Rev. Lett._ 91, 120403 (2003).
- C. M. Caves, C. A. Fuchs, K. K. Manne, J. M. Renes, «Gleason-type derivations of the quantum probability rule for generalized measurements», _Found. Phys._ 34, 193 (2004).
- W. H. Zurek, «Environment-assisted invariance, entanglement, and probabilities in quantum physics», _Phys. Rev. Lett._ 90, 120404 (2003).
- D. Deutsch, «Quantum theory of probability and decisions», _Proc. R. Soc. Lond. A_ 455, 3129 (1999).
- D. Wallace, _The Emergent Multiverse_, Oxford University Press, 2012.
