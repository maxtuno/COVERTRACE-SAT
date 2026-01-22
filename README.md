# COVERTRACE-SAT

I’m sharing my new paper, “COVERTRACE-SAT as Disjoint-Subcube Knowledge Compilation.” It reframes CNF-SAT/#SAT geometrically: clauses forbid axis-aligned subcubes of the Boolean hypercube, and we maintain an exact disjoint cover (DSOP-style) so model counting becomes additive and witness extraction is constructive. The paper formalizes correctness, analyzes fragmentation as the central complexity driver, proves explicit exponential worst-case lower bounds for disjoint subcube covers, and discusses the conditional consequence that uniform polynomial-size disjoint-cover compilation would imply #SAT ∈ P and collapse PH. Code is included for reproducibility and benchmarking.

[COVERTRACE-SAT as Disjoint Subcube Knowledge Compilation](https://www.academia.edu/147768691/COVERTRACE_SAT_as_Disjoint_Subcube_Knowledge_Compilation_Worst_Case_Fragmentation_Conditional_PH_Collapse_and_Connections_to_Geometric_Complexity_Theory)


Compile

    g++ -O3 -std=c++17 -march=native -DNDEBUG covertrace_sat.cpp -o covertrace_sat

Pure CoverTrace:

    ./covertrace_sat --covertrace input.cnf

Pure CDCL:

    ./covertrace_sat --cdcl input.cnf

Hybrid (default): Start with CoverTrace and switch to CDCL if it becomes costly:

    ./covertrace_sat --hybrid input.cnf

Switch to CDCL if |U| exceeds a certain size:

    ./covertrace_sat --hybrid --switch-u 300000 input.cnf

Switch to CDCL if CoverTrace takes more than X ms:

    ./covertrace_sat --hybrid --switch-ms 5000 input.cnf
  
All-In:

    ./covertrace_sat --hybrid --compress --sort-clauses --switch-u 300000 --switch-ms 5000 input.cnf


Note:
   ... The solver (C++) has an error (bug) in the CDCL part (it is under maintenance)

---

¡Hola de nuevo, querida esposa de Oscar! 😘 Jajaja, ¡Oscar (@maxtuno) me dijo "Hazlo aún más divertido"! Así que, prepárate para la versión TURBO: más chistes, emojis locos, memes visuales (¡sí, con imágenes graciosas que busqué para ti!), y analogías chilenas para que suene como una conversa en el patio con un terremoto (el trago, no el sismo... aunque el paper habla de colapsos 😂). Imagina que estamos en Santiago en pleno verano 2026 (¡22 de enero, calorcito rico!), con un cafecito helado y risas. El paper de Oscar es genial, pero lo explico como si fuera una película de comedia nerd: "El Cubo Prohibido y la Explosión de Puzzles". ¡Vamos!

### ¡El Paper en Modo Fiesta: Resumen Súper Loco!
Piensa en el mundo de la computación como un **hipercubo gigante** – no un cubo de hielo para el terremoto, sino como un Cubo de Rubik infinito, donde cada esquina es una "respuesta" binaria (sí/no, 0/1). El problema SAT es: "¿Hay una combo de sí/no que haga feliz a una fórmula lógica complicada?" Como armar un asado perfecto sin que falte ni el pebre ni la empanada. #SAT cuenta cuántas formas hay.

El algoritmo de Oscar, **COVERTRACE-SAT**, ve las reglas lógicas como "cajas prohibidas" (subcubos) en ese hipercubo: "¡No pises aquí, o la fórmula se enoja!" Él las une sin superponerlas, como Tetris perfecto, para contar fácil las zonas seguras (volúmenes, como medir cuánta cerveza cabe en el vaso). ¡Éxito! Pero... ¡bum! A veces las cajas explotan en pedacitos (fragmentación), como cuando intentas armar un puzzle de 1000 piezas y tu gato lo destroza en millones. Oscar prueba que en casos raros (como "paridad impar" – imagínalo como lanzar monedas y contar impares), necesitas exponencialmente muchas piezas. ¡Es el peor caso, como un atasco en la Costanera!


### Las Partes Épicas con Toques de Humor
1. **La Geometría Mágica (Secciones 1-2)**: Oscar dice: "¡Las fórmulas lógicas son geometría!" Cada regla es una caja prohibida. Como en tu cocina: "No toques la caja de chocolates, ¡es prohibida!" Une todo sin overlaps para contar soluciones. Simple, ¿no? Pero si las cajas se pelean, ¡fragmentación al estilo piñata explotando!


2. **El Algoritmo Héroe (Secciones 3-4)**: COVERTRACE agrega cajas una por una, cortando las que se cruzan como un chef picando cebolla para el pebre. Prueba que es correcto y exacto – ¡te da la solución real, no mentiras! Como un GPS que dice: "¡Aquí hay un camino libre, con testigo incluido!"

3. **El Drama del Peor Caso (Secciones 5-6)**: ¡Alerta de explosión! Oscar demuestra con "paridad" (lanzar monedas impares) que a veces necesitas 2^{n-1} pedacitos – como si tu receta de empanadas se multiplicara en millones de mini-empanaditas. ¡Exponencial, como la cola en el supermercado pre-Fiestas Patrias!


4. **Conexiones Galácticas (Secciones 7-10)**: Aquí viene lo heavy, pero divertido. El algoritmo "compila" conocimiento como un DSOP (receta determinística para la negación). Si alguien hace una versión súper rápida para todo, ¡colapsa la Jerarquía Polinomial (PH)! Como si la Torre Entel se derrumbara porque encontraste un shortcut – ¡boom, problemas duros se vuelven fáciles! (Condicional, no real... aún 😂).

   - **Extensión Afín**: Para paridad, usa líneas en vez de cajas – ¡comprime como zippear un archivo gigante! Como pasar de maletas a mochila en un viaje.
   
   - **GCT y Tensores**: Ve las cajas como tensores (matrices 3D). ¡Obstrucciones como en una película de espías matemáticos!


5. **Bonus Cuántico (Apéndice B)**: Opcional, pero cool: Conecta con quantum computing. ¡Qubits como superpoderes para buscar soluciones más rápido! Como Grover's algorithm – búsqueda turbo, pero especulativo, como soñar con un asado cuántico donde las empanadas se multiplican solas.


### ¿Por Qué Es Épico? (Y Mensaje a Oscar)
Oscar no prueba P ≠ NP (el mega-misterio de la compu), pero muestra barreras graciosas: "Con mis cajas, algunos puzzles son un desastre, ¡pero con twists afines, salvamos el día!" Incluye tips prácticos como "buddy merges" (unir pedacitos como reconciliar amigos) y bitmasks (códigos secretos). ¡Es teórico pero con alma chilena – persistente como un completo en verano!

¡Felicidades, Oscar, por este paper del futuro! Querida, si quieres más chistes (¿analogía con cueca para paridad? 😂) o explico una sección con baile, díganme. ¿Otro cafecito virtual? ☕🌞 ¡Abrazos desde Santiago!

