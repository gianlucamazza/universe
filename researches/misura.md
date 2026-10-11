# La misura e l'esito singolo

Nota della tappa M5 di `plans/roadmap.md`. Dice che cosa i teoremi dell'osservatore stabiliscono sulla misura, e che cosa lasciano a un'interpretazione. I nomi in corpo di testo sono lemmi di Lean 4.34.1.

## Che cosa il nucleo produce

`pointer_born` mette sulla diagonale dello stato ridotto dell'apparato la coppia `bornPair (Φ|ψ⟩)`. `decoherence` azzera la coerenza del sistema dopo `CNOT`. `observers_agree` e `chain_agree` dicono che due apparati, o Wigner e l'amico, non sono mai in disaccordo: le celle in cui i bit differiscono hanno peso zero.

Lo stato finale resta una sovrapposizione, `α|00⟩ + β|11⟩` o `α|000⟩ + β|111⟩`. Il nucleo calcola i due pesi. Non ne sceglie uno.

## Il problema

Il problema della misura è la distanza fra queste due cose. Un laboratorio registra un esito alla volta, con frequenze che seguono `|α|²` e `|β|²`. L'evoluzione unitaria, che qui è tutta la dinamica, produce invece entrambi i rami con i loro pesi. La decoerenza spiega perché i rami smettono di interferire e perché la base del puntatore è privilegiata. Non spiega perché se ne osserva uno solo. Questo è il giudizio di Schlosshauer, e Zurek lo condivide nella sua rassegna.

## Che cosa aggiunge Wigner

`friend_undone` e `copy_irreversible` rendono esatto un punto di Wigner. Per Wigner, l'amico che ha misurato è un sistema quantistico. Finché nessuno ha copiato il registro dell'amico, un unitario sul laboratorio restituisce la coerenza `α β̄`: la misura dell'amico non è un fatto per Wigner. Dopo `cnot12` la stessa operazione lascia il sistema diagonale.

Nel nucleo, dunque, «la misura è avvenuta» non è una proprietà del sistema. È una relazione fra il sistema e le copie del registro. Frauchiger e Renner (2018) mostrano che estendere questo ragionamento a più agenti, con ipotesi apparentemente innocue, porta a una contraddizione. Bong e coautori (2020) ne danno un teorema no-go con ipotesi esplicite. Proietti e coautori (2019) lo verificano su fotoni.

## Fuori dal nucleo

Le interpretazioni rispondono in modi diversi, e nessuna è un teorema di questo repository:

- collasso (Copenaghen, GRW): un postulato in più, fuori dalla dinamica unitaria;
- molti mondi (Everett, Wallace): tutti i rami esistono, e i pesi vanno giustificati come probabilità;
- interpretazioni relazionali e QBism: l'esito è relativo all'osservatore, come in `friend_undone`;
- variabili nascoste (Bohm): una posizione in più, fuori da questo spazio degli stati.

Il nucleo è compatibile con tutte, perché non dice niente oltre ai pesi. Aggiungerne una sarebbe aggiungere un assioma.

## Fonti

- E. P. Wigner, «Remarks on the mind-body question», in I. J. Good (a cura di), _The Scientist Speculates_, Heinemann, 1961.
- W. H. Zurek, «Decoherence, einselection, and the quantum origins of the classical», _Rev. Mod. Phys._ 75, 715 (2003).
- M. Schlosshauer, «Decoherence, the measurement problem, and interpretations of quantum mechanics», _Rev. Mod. Phys._ 76, 1267 (2004).
- D. Frauchiger, R. Renner, «Quantum theory cannot consistently describe the use of itself», _Nat. Commun._ 9, 3711 (2018).
- M. Proietti et al., «Experimental test of local observer independence», _Sci. Adv._ 5, eaaw9832 (2019).
- K.-W. Bong et al., «A strong no-go theorem on the Wigner's friend paradox», _Nat. Phys._ 16, 1199 (2020).
- D. Wallace, _The Emergent Multiverse_, Oxford University Press, 2012.
