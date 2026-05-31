// Mit Typst >= 0.14.x kompilieren: typst compile logicutils.typ
#set document(title: "logicutils — Eine sanfte Einführung", author: "NEWSNIPER")
#set page(paper: "a4", margin: 2.2cm, numbering: "1")
#set par(justify: true, leading: 0.7em)
#set text(font: "New Computer Modern", size: 11pt, lang: "de")
#set heading(numbering: "1.1")
#show heading.where(level: 1): it => [
  #pagebreak(weak: true)
  #block(below: 1.0em, text(weight: "bold", size: 18pt, it.body))
]
#show raw.where(block: true): it => block(
  fill: luma(245), inset: 8pt, radius: 3pt, width: 100%, it
)

#align(center)[
  #text(size: 22pt, weight: "bold")[logicutils]
  #v(0.4em)
  #text(size: 14pt)[Eine sanfte Einführung für Anfängerinnen und Anfänger]
  #v(2em)
]

#outline(indent: auto)

= Warum gibt es dieses Projekt?

Sie haben vermutlich schon Ihre ersten Programme geschrieben — vielleicht ein
kleines C-Programm, das Sie mit `gcc` übersetzen, oder ein Python-Skript, das
Sie mit `python3` ausführen. Anfangs sind die Programme winzig und Sie rufen
den Übersetzer von Hand auf. Sehr bald wird jedes Projekt jedoch groß genug,
dass die Handarbeit lästig wird. Drei besondere Schmerzen tauchen immer
wieder auf:

+ *Wiederholung*. Sie ändern eine Quelldatei und müssen sich merken, welche
  Ausgaben davon abhängen, damit Sie genau diese neu erzeugen.
+ *Muster*. Viele Aufgaben haben dieselbe Form ("übersetze jede `.c`-Datei
  in diesem Verzeichnis in eine `.o`-Datei"); jede einzeln auszuschreiben
  ist mühsam.
+ *Buchführung*. Sie möchten _wissen_, ob eine Datei aktuell ist, statt
  zu raten. In einem Team wird "aktuell aus wessen Sicht?" zu einer ernsten
  Frage.

Die klassische Antwort darauf ist ein _Build-System_ wie Make. Make ist
ungefähr fünfzig Jahre alt. Es funktioniert, und Sie sollten es lernen, doch
es hat bekannte Schwächen: Es entscheidet meist allein anhand von
Änderungszeiten, was neu zu bauen ist; seine Sprache ist klein und brüchig;
und es für wissenschaftliche Pipelines oder KI-Trainingsläufe zu erweitern,
ist umständlich.

Eine modernere Antwort ist BioMake, ein experimentelles Werkzeug aus der
Bioinformatik, das einige dieser Schwächen behebt, indem es _logische
Programmierung_ auf Make aufsetzt. Logische Programmierung — die Sie später
unter dem Namen "Prolog" wiedersehen werden — erlaubt es, mit Regeln und
Fakten zu beschreiben, was als gültige Build-Konfiguration zählt, und einen
Suchalgorithmus die Antwort finden zu lassen. BioMake ist klug entworfen,
leidet aber an einem anderen Problem: Es ist ein einziges großes Werkzeug,
das Make _ersetzen_ statt mit ihm zusammenarbeiten möchte.

*logicutils* versucht, die guten Ideen von BioMake — Mehrfach-Wildcard-Muster,
inhaltsbasierte Frische, logische Programmierung, Cluster-Unterstützung — zu
übernehmen und in einen _Werkzeugkasten_ umzuformen, der mit der von Ihnen
ohnehin verwendeten Shell und dem Build-System kooperiert. Jedes Werkzeug
erledigt eine Aufgabe gut, im Geiste der klassischen Unix-Philosophie.
Zusammen decken sie denselben Boden ab wie ein Build-System, aber Sie selbst
fügen die Teile zusammen.

Dieses Dokument erklärt, was diese Werkzeuge sind und wie man mit ihnen
denkt. Es setzt voraus, dass Sie ein kleines Shell-Skript lesen können und
grundlegende algorithmische Begriffe (Graphen, Hashing, Rekursion) erkennen.
Vorkenntnisse zu Build-Systemen, logischer Programmierung oder Cluster-
Computing sind _nicht_ nötig — diese Themen werden bei Bedarf von Grund auf
eingeführt.

= Ein kurzer Rundgang

#figure(
  table(
    columns: (auto, 1fr),
    align: (left, left),
    inset: 6pt,
    stroke: 0.5pt + luma(180),
    [*Werkzeug*], [*Einzeiler*],
    [`freshcheck`], [Entscheidet, ob ein Ziel aktuell ist.],
    [`stamp`],      [Erfasst Datei-Signaturen (Hashes, Größen, …).],
    [`lu-match`],   [Vergleicht ein Muster mit benannten Wildcards mit einem String.],
    [`lu-expand`],  [Erzeugt Kombinationen aus Wertemengen.],
    [`lu-query`],   [Stellt logische Fragen an Fakten und Regeln.],
    [`lu-rule`],    [Findet eine Regel, die ein Ziel erzeugt.],
    [`lu-queue`],   [Reicht Aufträge an lokale oder Cluster-Scheduler.],
    [`lu-par`],     [Führt einen Graphen abhängiger Aufgaben parallel aus.],
    [`lu-deps`],    [Liest, transformiert und analysiert Abhängigkeitsgraphen.],
    [`lu-multi`],   [Eine einzige Binärdatei, die alle obigen Werkzeuge enthält.],
  ),
  caption: [Die neun Werkzeuge (und die Multicall-Binary).],
)

Im Folgenden erläutern wir für jedes Werkzeug das gelöste Problem, die
zugrunde liegende Idee in einfachen Worten und ein kleines Beispiel.
Sobald eine Idee größer ist als ein Absatz (etwa inhaltsbasierte Frische
oder logische Programmierung), halten wir kurz inne und erklären sie von
Grund auf.

= Wann ist eine Datei "frisch"?

== Der naive Ansatz

Wenn `make` entscheidet, ob `main.o` neu gebaut werden muss, vergleicht es
die Änderungszeit von `main.o` mit der von `main.c`. Ist `main.c` neuer,
wird `main.o` neu gebaut. Das ist schnell — das Betriebssystem speichert
diese Zeitstempel ohnehin — und meistens richtig.

Es scheitert aber auf überraschende Weise. Wenn Ihr Editor `main.c`
speichert, obwohl Sie nur kurz hineingeschaut haben, baut Make `main.o`
neu, obwohl der Inhalt unverändert ist. Wenn Sie eine Datei mit einem
Werkzeug kopieren, das Zeitstempel zurücksetzt, hält Make die Kopie für
älter als die Ausgabe und überspringt den Neubau, obwohl die Bytes
verschieden sind. Wissenschaftliche Build-Systeme und KI-Pipelines sind
früh in solche Fallen gelaufen, und eine andere Idee — _inhaltsbasierte
Frische_ — wurde nach und nach Standard.

== Inhaltsbasierte Frische

Anstatt Zeitstempel zu vergleichen, vergleichen wir den _Inhalt_ von
Dateien. Da wir nicht jedes Mal die ganze Datei lesen können, fassen wir
sie zu einem Fingerabdruck fester Länge zusammen, dem _Hash_. Eine gute
kryptografische Hash-Funktion wie BLAKE3 oder SHA3 hat die Eigenschaft,
dass jede Änderung der Datei zu einem völlig anderen Fingerabdruck führt.
Stimmt der Fingerabdruck von `main.c` mit dem überein, der beim letzten
Bau von `main.o` aufgezeichnet wurde, können wir den Neubau überspringen,
selbst wenn der Zeitstempel etwas anderes behauptet.

Der Haken: Wir brauchen einen Ort, der den Fingerabdruck vom letzten Mal
behält. Genau das macht `stamp`: Es legt Fingerabdrücke in einem kleinen
Verzeichnis namens `.lu-store/` neben dem Projekt ab. `freshcheck` ist
dann das Werkzeug, das `stamp` fragt: "Ist der gespeicherte Fingerabdruck
dieser Datei noch aktuell?"

== Erstes Beispiel

```sh
# main.o nur dann neu bauen, wenn der Inhalt von main.c sich geändert hat.
freshcheck --method=hash main.o main.c || gcc -c main.c -o main.o
stamp record --method=hash main.o
```

`freshcheck` schweigt im Erfolgsfall und beendet sich mit Status 0; im
Misserfolg mit Status 1. Daher führt das Shell-Kurzschluss-`||` den
Compile-Befehl nur aus, wenn die Datei veraltet ist. Nach dem Bau
aktualisiert `stamp record` den Fingerabdruck, sodass der nächste Lauf
wieder überspringen kann.

Sie mögen fragen, warum es `stamp` _und_ `freshcheck` getrennt gibt. Der
Grund ist die Unix-Designregel: Jedes Werkzeug erfüllt genau eine Aufgabe.
`stamp` kennt die Speicherung; `freshcheck` kennt die Politik. Möchten Sie
Zeitstempel mit Größen und Hashes kombinieren, ändern Sie nur die Flags
von `freshcheck`, ohne das Speicher-Backend anzufassen.

== Verschiedene Vergleichsverfahren

`freshcheck` akzeptiert mehrere Methoden, die mit `--combine=any` oder
`--combine=all` gestapelt werden können:

- `timestamp`: der klassische Make-Ansatz — schnell, manchmal falsch.
- `hash`: der inhaltsbasierte Ansatz von oben. Sehr stark, etwas langsamer.
- `checksum`: ein schnellerer, aber schwächerer Fingerabdruck (CRC-32).
  Nützlich auf eingeschränkter Hardware, wo kryptografisches Hashing zu
  teuer ist.
- `size`: die Bytelänge der Datei. Trivial, aber als Tie-Breaker neben
  `timestamp` praktisch — fängt Fälle ab, in denen Inhalt und Zeitstempel
  auseinanderlaufen.
- `always`: niemandem trauen, jedes Mal neu bauen. Beim Debuggen nützlich.

= Viele Dateien auf einmal benennen

== Muster sind überall

Software-Projekte haben selten mit einer einzelnen Datei zu tun. "Übersetze
jede `.c` in eine `.o`" oder "verarbeite jede FASTQ in eine BAM" ist die
Regel, nicht die Ausnahme. Make hat dafür `%`-Regeln, doch `%` steht für
genau eine Wildcard, und reale Probleme verlangen oft zwei oder mehr.

Stellen Sie sich einen bioinformatischen Workflow vor: viele _Proben_ und
mehrere _Referenzen_, und für jedes Paar (Probe, Referenz) eine
ausgerichtete Datei:

```
align-sample1-hg38.bam
align-sample1-mm10.bam
align-sample2-hg38.bam
align-sample2-mm10.bam
…
```

Sie möchten _eine_ Regel schreiben, deren Muster sagt: "Für jede Probe $X$
und jede Referenz $Y$ wird `align-X-Y.bam` aus `X.fastq` und `Y.fa` gebaut."
In Make wird das umständlich; in `lu-match` ist es selbstverständlich.

== Syntax von `lu-match`

Ein Muster ist ein String, in dem `\u{7B}NAME\u{7D}` (geschweifte Klammern um einen
Bezeichner) eine benannte Wildcard kennzeichnet. Standardmäßig passt eine
Wildcard auf genau einen Pfadabschnitt (keine Schrägstriche). Andere
Varianten gibt es; vorerst denken Sie sich `\u{7B}X\u{7D}` als "irgendein Block
aus Buchstaben und Ziffern".

Eine Eingabe vergleichen:

```sh
$ lu-match 'align-{X}-{Y}.bam' align-sample1-hg38.bam
X=sample1
Y=hg38
```

Erscheint derselbe Name zweimal, fordert der Matcher, dass beide Stellen
denselben Wert annehmen:

```sh
$ lu-match '{stem}.tar.{stem}'   # exotisch: gleiches Wort vorn und hinten
```

Diese Gleichheitsprüfung heißt _Unifikation_ und ist die zentrale
Operation der logischen Programmierung. Wir treffen sie in `lu-query`
wieder.

== `lu-expand`: die Matrix erzeugen

`lu-match` antwortet auf "Welcher Name bindet welche Wildcards?".
`lu-expand` antwortet auf das Gegenteil: "Welche Namen erzeuge ich aus
diesen Wildcard-Werten?".

```sh
lu-expand --var 'S=s1,s2,s3' --var 'R=hg38,mm10' \
          --filter 'S != R' \
          'align-{S}-{R}.bam'
```

Das druckt das kartesische Produkt von $S$ und $R$, ohne die Zeilen, in
denen `S != R` falsch ist. Genau das kartesische Produkt aus der diskreten
Mathematik. `lu-expand` durchläuft die Paare wie ein Tachometer: die
rechteste Variable wechselt am schnellsten.

`lu-match` und `lu-expand` bilden zusammen die Musterebene des Werkzeugkastens:
Sie gehen entweder von konkreten Dateinamen zu Wildcard-Werten (Matching)
oder umgekehrt (Expansion).

= Von Regeln zur Logik

== Regeln im Kleinen

Eine klassische Makefile-Regel ist ein Tripel aus Muster, Abhängigkeiten
und Rezept:

```
%.o: %.c
	$(CC) -c $< -o $@
```

`lu-rule` hebt dies auf mehrere Wildcards:

```
pattern: align-{X}-{Y}.bam
deps:    {X}.fastq {Y}.fa
recipe:  bwa mem {Y}.fa {X}.fastq > align-{X}-{Y}.bam
goal:    X != Y
```

Die optionale Zeile `goal` ist eine Nebenbedingung. Sieht `lu-rule` ein
Ziel wie `align-sample1-hg38.bam`, dann (i) versucht es das Muster zu
unifizieren, (ii) prüft, ob `goal` für die Bindungen gilt, und (iii) gibt
erst dann die expandierten `deps` und `recipe` aus.

Das Feld `goal` ist ein Hinweis auf etwas Größeres. `goal: X != Y` ist
eine kleine logische Formel. Was, wenn wir längere Formeln wollten? Was,
wenn `goal` andere Regeln aufrufen könnte? Was, wenn die Engine statt eines
Wahrheitswertes _alle_ Belegungen aufzählen könnte, die das Ziel wahr
machen?

Das ist logische Programmierung — sie verdient einen eigenen Abschnitt.

== Ein kurzer Abstecher in die logische Programmierung

Logische Programmierung verlangt, die Welt deklarativ zu beschreiben — mit
_Fakten_ und _Regeln_ — und dann _Anfragen_ zu stellen, deren Antwort die
Engine sucht. Die berühmteste Sprache dafür ist Prolog; die Ideen hier
ähneln Prolog, sind aber nicht identisch.

Ein *Fakt* ist eine Aussage, die wir als wahr akzeptieren:

```
parent(alice, bob)
parent(bob,   carol)
```

Eine *Regel* leitet neue Fakten aus alten ab:

```
rule grandparent(X, Z):
    parent(X, Y)
    parent(Y, Z)
```

Eine *Anfrage* ist eine Frage:

```
?  grandparent(alice, Who)
```

Die Engine sucht Belegungen für `Who`, die `grandparent(alice, Who)` wahr
machen. Hier findet sie `Who = carol`. Sie probiert Kandidaten und
_unifiziert_ Variablen mit konkreten Werten — dieselbe Unifikation wie bei
`lu-match`.

logicutils bringt eine Wissensbasissprache mit, KB genannt (genaueres in
#link(<kb-language>)[Abschnitt 7]), und das Werkzeug `lu-query`, das KB-Dateien liest und
Anfragen beantwortet. KB hat Fakten und Regeln wie Prolog plus drei
Ideen, die Sie in Standard-Prolog _nicht_ finden: _Abduktion_,
_Constraints_ und _Typrelationen_.

== Abduktion in einem Absatz

Deduktion geht von Regeln und Fakten zu Schlussfolgerungen. _Abduktion_
geht den umgekehrten Weg: Gegeben eine erwünschte Schlussfolgerung und
die Regeln der Welt — welche Fakten würden, wenn sie wahr wären, die
Schlussfolgerung erklären? Im Build-Kontext genau die Frage: "Was müsste
ich tun, damit dieses Ziel aktuell ist?". KB stellt Abduktion direkt mit
dem Schlüsselwort `abduce` zur Verfügung:

```
abduce missing_source(File):
    depends(Target, File)
    not exists(File)
    explain "source file may need generation"
```

== Constraints

Ein Constraint ist eine logische Bedingung, die die Engine beobachtet,
während Variablen gebunden werden. Sobald eine beobachtete Variable
festgelegt ist und die Bedingung verletzt, springt die Suche zurück.
Constraints lassen sich Aussagen wie "diese Analyse gilt nur, wenn
`quality >= 30`" natürlich ausdrücken, und die Engine wendet sie so früh
wie möglich an.

== Warum das für Builds wichtig ist

Ein Build-System ist im Grunde eine logische Theorie: Ziele existieren,
Dateien hängen voneinander ab, Rezepte erzeugen Dateien, Frische erlaubt
das Überspringen. Mit einer Logik-Engine kann man interessante Anfragen
stellen:

- _Welche Ziele sind veraltet?_
- _Welches kleinste Set an Dateien müsste ich neu erzeugen, um Ziel $T$
  aktuell zu machen?_
- _Warum wird $T$ neu gebaut? Was hat die Engine geschlussfolgert?_

Klassische Build-Systeme beantworten eine feste Untermenge dieser Fragen.
Mit `lu-query` stellen Sie die Frage, die heute passt.

= Die KB-Sprache <kb-language>

== Form einer KB-Datei

KB ist einrückungsempfindlich wie Python. Einrückung öffnet einen Block,
Ausrückung schließt ihn. Zeilen mit `#` sind Kommentare. Jede Konstruktion
auf oberster Ebene beginnt mit einem Schlüsselwort: `fact`, `rule`,
`abduce`, `constraint`, `fn`, `type`, `data`, `relation`, `instance`,
`import`, `export`.

```
fact depends:
    main.o    <- main.c
    main.o    <- header.h
    parser.o  <- parser.c

rule stale(Target):
    depends(Target, Dep)
    newer(Dep, Target)

constraint valid_alignment(x: SampleId, y: Reference):
    x != y
    exists("{x}.fastq")
```

== Funktionale Programmierung in KB

Die meisten Logik-Probleme enthalten einige rein _berechnende_ Schritte,
die nichts mit Suche zu tun haben. KB lässt Sie diese als Funktionen
schreiben — in einer kleinen funktionalen Untersprache, die in der Stimmung
an Haskell oder Scala erinnert, aber viel kleiner ist. Funktionen sind
rein (kein I/O), kennen Lambdas (`x => expr`) und einen
Pipeline-Operator von links nach rechts `|>`:

```
fn stem(path):
    path |> split(".") |> head

fn align_cmd(sample, ref):
    "bwa mem {ref}.fa {sample}.fastq"
```

Funktionen lassen sich aus Regelkörpern aufrufen, sodass sich logische und
berechnende Schritte natürlich verschränken.

== Graduelle Typisierung

Typen sind optional. Wer sie schreibt, lässt den Parser prüfen, ob Aufrufe
zu Deklarationen passen. Wer sie weglässt, lebt mit dynamischer Behandlung.
Dieser _graduelle_ Ansatz erlaubt Anfängern, ohne Typen zu beginnen und sie
später nachzuziehen:

```
fn align_cmd(sample: String, ref: String) -> Command:
    "bwa mem {ref}.fa {sample}.fastq"

type SampleId = String where matches("[A-Z]{2}[0-9]+")
```

Die `where`-Klausel hängt eine Verfeinerung an: Eine `SampleId` ist ein
String, der zusätzlich das reguläre Muster erfüllt. Verfeinerungen
verschmelzen mit Constraints — fließt ein Wert in eine Position vom Typ
`SampleId`, prüft die Engine die Verfeinerung.

== Typrelationen und verschachtelte Instanzen

Sie wollen eine Funktion schreiben, die Reads ausrichtet, doch wie sie das
tut, hängt von der Queue ab (lokal, SLURM, GPU, …). Viele Sprachen lösen
das mit einer Schnittstelle oder einem Trait; KB nennt den Mechanismus
_Relation_ und nimmt mehr als einen Typ-Parameter gleichzeitig:

```
relation Processable(Input, Output, Engine):
    fn process(input: Input, engine: Engine) -> Output
```

Sie liefern dann _Instanzen_ der Relation. Eine Instanz für eine bestimmte
Typkombination implementiert die Funktion. Instanzen dürfen überall
deklariert werden — sie müssen nicht im Relationsblock stehen — und sie
können _verschachtelt_ sein:

```
instance Processable(Dataset, Model, GPU):
    fn process(data, engine):
        train(data)

    instance Batchable(Dataset, Model) where Engine == GPU:
        fn batch_size(input): estimate_vram(input)

        instance Shardable(Dataset) where Dataset == LargeDataset:
            fn shard_count(input): input.size / max_shard_size
```

Eine verschachtelte Instanz erbt _jede_ `where`-Klausel ihrer Vorfahren.
Die innerste Instanz greift nur, wenn `Engine == GPU` _und_ `Dataset ==
LargeDataset`. So lassen sich geschichtete Vorbedingungen ausdrücken,
ohne sie wiederholt aufzuschreiben.

== Importe und Module

Eine KB-Datei ist ein Modul. Sie können ein Projekt auf mehrere Dateien
aufteilen und Teile in den Geltungsbereich holen:

```
import bio.alignment (align, index)
import utils.paths   as P
```

`import` darf auch innerhalb eines Blocks stehen. Dann leben die
eingeführten Bindungen nur so lange wie der Block. Praktisch, um in großen
Projekten den globalen Namensraum sauber zu halten.

= Parallel ausführen

== Vom Graphen zum Plan

Wenn Sie wissen, welche Ziele veraltet sind und wer von wem abhängt, haben
Sie einen gerichteten azyklischen Graphen (DAG). Ihn effizient zu bauen
heißt, Knoten so zu planen, dass Abhängigkeiten vor ihren Abhängigen
fertig werden, und unabhängige Arbeit parallel zu erledigen. Genau dies
tut `lu-par`.

Eingabe für `lu-par` ist eine kleine Textdatei mit einer Zeile pro Aufgabe:

```
ID<TAB>DEP1,DEP2<TAB>COMMAND
```

`lu-par` prüft mit Kahns Algorithmus (topologische Sortierung), dass der
Graph azyklisch ist, und schickt Aufgaben in einen Worker-Thread-Pool. Wenn
ein Worker fertig ist, wird der Eingangsgrad jedes Nachfolgers verringert;
Nachfolger mit Grad 0 werden lauffähig.

== Vom Fehler erholen

Reale Workflows scheitern gelegentlich. `lu-par` bietet drei nützliche
Verhaltensweisen:

- `--retry=N` führt eine fehlgeschlagene Aufgabe bis zu $N$-mal erneut
  aus. Praktisch bei flackrigen Tests oder transienten Netzwerkfehlern.
- `--keep-going` lässt unabhängige Zweige weiterlaufen, auch wenn ein
  Geschwister scheitert.
- `--transaction` behandelt den ganzen DAG als atomare Operation: scheitert
  irgendeine Aufgabe nach allen Wiederholungen, werden die
  Frische-Einträge der bereits fertigen Aufgaben über `stamp`
  zurückgenommen, sodass der nächste Lauf diese Ziele wieder als veraltet
  sieht. Gemeinsam mit inhaltsbasierter Frische ist das ein kleines, aber
  wirksames Sicherheitsnetz.

== Über eine Maschine hinaus: Queues

Wenn die Maschine vor Ihnen nicht reicht, geben Sie Arbeit an einen
Cluster ab. Ein Cluster ist abstrakt eine Queue: Sie übergeben eine
Beschreibung dessen, was laufen soll, und erhalten eine Kennung, mit der
Sie den Fortschritt erfragen können. Verschiedene Systeme (SLURM, SGE,
PBS, …) haben unterschiedliche Befehle und Optionen, doch die Idee ist
dieselbe.

`lu-queue` legt diese Idee hinter eine einzige CLI:

```sh
JID=$(lu-queue submit --engine=slurm --slots=4 --mem=16G -- \
      align sample1 hg38)
lu-queue wait "$JID"
```

Mit `--engine=local` läuft die Planung in Worker-Threads des aktuellen
Prozesses; `--engine=slurm` übersetzt die generischen Optionen in die
nativen SLURM-Optionen. Vom Laptop zum Cluster wird zur einzigen
Option-Änderung.

= Ein durchgespieltes Beispiel

Wir schließen mit einem Beispiel, das die meisten Bausteine zusammenführt:
ein kleiner Build, der alle C-Dateien zu Object-Dateien übersetzt, mit
inhaltsbasierten Fingerabdrücken Veraltetheit feststellt und parallel
arbeitet.

== Aufbau

```
project/
├── src/main.c
├── src/util.c
└── include/util.h
```

== Schritt 1: Abhängigkeitsgraph erzeugen

Mit `gcc` bestimmen wir, welche `.c` welche `.h` einbindet:

```sh
gcc -M -MM -Iinclude src/*.c
```

`gcc` druckt Regeln der Form `main.o: src/main.c include/util.h`. Wir
leiten das in `lu-deps`, damit es das von `lu-par` erwartete Format
erhält:

```sh
gcc -M -MM -Iinclude src/*.c \
| lu-deps --from=gcc --to=tsv > deps.tsv
```

`deps.tsv` hat nun pro Object-Datei eine Zeile mit deren Abhängigkeiten.

== Schritt 2: in ausführbare Aufgaben verwandeln

Jeder Zeile fehlt die Befehlsspalte. Ein kurzes `awk` setzt sowohl den
Compiler-Aufruf als auch die Frischeprüfung ein:

```sh
awk -F'\t' 'BEGIN{OFS="\t"} {
    cmd = "freshcheck --method=hash " $1 " " $2 \
          " || gcc -c " $1 ".c -o " $1
    print $1, $2, cmd
}' deps.tsv > tasks.tsv
```

== Schritt 3: parallel bauen

```sh
lu-par -j 4 --progress --transaction --taskfile tasks.tsv
```

`-j 4` heißt vier Worker; `--progress` schreibt Start- und Endmeldungen
nach stderr; `--transaction` rollt den Frische-Speicher bei einem Fehler
zurück.

== Schritt 4: neue Fingerabdrücke speichern

Nach erfolgreichem Lauf werden die neuen Inhalt-Fingerabdrücke gespeichert,
damit der nächste Lauf überspringen kann:

```sh
stamp record --method=hash *.o
```

Liest man die vier Schritte am Stück, sieht man die Philosophie am Werk:
Kein Werkzeug ist für die ganze Aufgabe verantwortlich; jedes erledigt
eine kleine Sache, und die Shell setzt sie zusammen. Wird die Anforderung
morgen anders — etwa Verteilung der Compiles auf einen SLURM-Cluster —
tauschen Sie ein einziges Werkzeug (`lu-par` gegen `lu-queue`); der Rest
bleibt.

= Wohin als Nächstes?

== Manpages

Jedes Werkzeug bringt eine Manpage in `docs/man/` mit. Sie sind knapp,
aber maßgeblich.

== Agenten-Referenz

Das Verzeichnis `docs/agents/` enthält eine strukturierte Referenz, die
für maschinelle Konsumenten (KI-Assistenten und Ähnliches) geschrieben
ist. Auch Menschen können sie lesen; sie ergänzt diese sanfte Einführung
gut, weil dort jede Option und jede Sonderfall an einer Stelle stehen.

== Die KB-Sprache ausprobieren

Lassen Sie die Tests mit `cargo test --workspace` laufen, um den Parser in
Aktion zu sehen, schreiben Sie dann eine kleine KB-Datei und stellen Sie
Anfragen mit `lu-query`. Beginnen Sie mit deduktiven Regeln; wenn sich das
vertraut anfühlt, probieren Sie Abduktion und Constraints.

== Etwas bauen

Der Werkzeugkasten ist am nützlichsten, wenn Sie ein echtes Problem haben.
Wählen Sie ein kleines Projekt — vielleicht den Build eines mehrsprachigen
Repositorys oder eine Datenpipeline — und versuchen Sie, es mit dem
Werkzeugkasten auszudrücken. Stoßen Sie auf etwas, das die Werkzeuge
direkt nicht können, fragen Sie sich, ob die Lücke in den Shell-Klebstoff
gehört oder in ein neues Werkzeug. Dieselbe Frage beantworten
Unix-Programmiererinnen und -Programmierer seit fünfzig Jahren.
