# Quanto dista dal nostro universo

Nota della tappa M5 di `plans/roadmap.md`. Dice che cosa il nucleo ha in comune con il nostro universo e che cosa lo separa, in ordine di distanza.

## In comune

Le regole del nucleo sono quelle della meccanica quantistica che regge ogni esperimento fatto finora: stati come vettori di ampiezze complesse, prodotto tensoriale per i sistemi composti, evoluzione unitaria, pesi come moduli quadri. Ogni teorema del repository vale per due o tre qubit isolati del mondo reale, e qubit così esistono: ioni intrappolati, circuiti superconduttori, fotoni. `CNOT`, la decoerenza di `decoherence` e il punto `(3/5, 4/5)` sono esperimenti da laboratorio.

## Che cosa separa

**Scala.** Il nucleo arriva a otto ampiezze, tre qubit, e la tappa M2 lo porta a `n` qualsiasi. Lloyd (2002) stima per l'universo osservabile una capacità dell'ordine di `10⁹⁰` bit, e lo spazio degli stati cresce come `2` elevato a quel numero. È una distanza di scala, non di natura.

**Spazio.** Nel nucleo non ci sono posizione né distanza. «Locale» vuol dire «su un fattore del prodotto tensoriale», come in `no_signalling_any_0`. Nel nostro universo la località viene dallo spazio-tempo, e la causalità relativistica è ciò che rende il no-signalling una legge e non una coincidenza.

**Campi.** La materia è descritta da campi quantistici, il Modello Standard, con particelle create e distrutte e interazioni fissate da simmetrie di gauge. I loro parametri sono una ventina di costanti misurate (Particle Data Group). Nel nucleo l'interazione è un generatore scelto, `G = |1⟩⟨1| ⊗ (n·σ)`.

**Tempo.** Qui il tempo è una coppia di simboli con `c² + s² = 1`. La tappa M3 li lega a un angolo razionale `φ` con le somme parziali della serie e un resto dimostrato (`Universe.Angle.circle_bound`), ma `cos φ` come numero reale resta fuori: senza i reali non c'è il limite. Nel nostro universo il tempo è continuo e fa parte dello spazio-tempo.

**Gravità.** Assente dal nucleo, e senza una teoria quantistica accettata nemmeno fuori (Kiefer). Qui la distanza non è nostra.

**Freccia del tempo.** Il nucleo è reversibile: `friend_undone` lo sfrutta. Nel nostro universo l'irreversibilità viene dall'entropia, da condizioni iniziali di bassa entropia (Albert) e dalla decoerenza con ambienti enormi. `copy_irreversible` ne mostra il meccanismo su un bit. Il mondo reale lo ripete su `10²³` molecole.

**Esito singolo.** Il nucleo produce i pesi e non sceglie un esito. Il nostro universo, per quanto se ne sa, fa lo stesso a livello delle leggi: è il problema della misura (`researches/misura.md`). La distanza qui non è nostra.

## In sintesi

Il nucleo ha la grammatica giusta e un vocabolario minimo. Scala e tempo sono distanze che le tappe M2 e M3 hanno ridotto: ogni numero di qubit, e il tempo fin dove arrivano i razionali. Spazio, campi e gravità sono distanze di natura: chiederebbero un altro nucleo, non un'estensione di questo.

## Fonti

- S. Lloyd, «Computational capacity of the universe», _Phys. Rev. Lett._ 88, 237901 (2002).
- S. Weinberg, _The Quantum Theory of Fields_, vol. 1, Cambridge University Press, 1995.
- Particle Data Group, «Review of Particle Physics», edizione corrente, pdg.lbl.gov.
- C. Kiefer, _Quantum Gravity_, 3ª ed., Oxford University Press, 2012.
- D. Z. Albert, _Time and Chance_, Harvard University Press, 2000.
- W. H. Zurek, «Decoherence, einselection, and the quantum origins of the classical», _Rev. Mod. Phys._ 75, 715 (2003).
