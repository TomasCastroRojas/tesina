# Tesina de grado LCC

Repositorio para el desarrollo de la tesina de grado para la Licenciatura en Ciencias de la Computación en la Universidad Nacional de Rosario.

El proyecto consiste en la formalización en Coq de un modelo de ataques cibernéticos basado en el framework MITRE ATT&CK. Se modelan técnicas de ataque, el estado de las máquinas del sistema y las capacidades del atacante, y se prueban invariantes que se preservan a lo largo de la ejecución de los ataques.

## Estructura del proyecto

```
tesina/
├── Attacker/
│   └── Attacker.v
├── Machine/
│   ├── Machine.v
│   ├── MachineAuxFunctions.v
│   ├── MachineValid.v
│   └── MachineView.v
├── Technique/
│   ├── Technique.v
│   ├── TechniqueOneStep.v
│   ├── TechniquePreCondition.v
│   └── TechniquePostCondition.v
├── Invariant/
│   ├── AuxLemmas/
│   │   ├── AuxLemmasAccount.v
│   │   ├── AuxLemmasEnviroment.v
│   │   ├── AuxLemmasFile.v
│   │   ├── AuxLemmasLogic.v
│   │   ├── AuxLemmasMachineUser.v
│   │   ├── AuxLemmasNeighbour.v
│   │   ├── AuxLemmasService.v
│   │   └── AuxTactics.v
│   ├── AttackerCapacity/
│   │   ├── AttackerAccess.v
│   │   └── AttackerReach.v
│   ├── ValidAttacker/
│   │   ├── ValidAttacker.v
│   │   ├── ValidAttackerI/
│   │   │   ├── ExploitationRemoteServices.v
│   │   │   ├── FileDirectoryDiscoveryLocal.v
│   │   │   ├── OneStepPreservesValidAttackerI.v
│   │   │   ├── RemoteServices.v
│   │   │   ├── RemoteSystemDiscovery.v
│   │   │   ├── SystemServiceDiscovery.v
│   │   │   └── UnsecuredCredentials.v
│   │   ├── ValidAttackerII/
│   │   │   └── (misma estructura que ValidAttackerI)
│   │   ├── ValidAttackerIII/
│   │   │   └── (misma estructura que ValidAttackerI)
│   │   └── ValidAttackerIV/
│   │       └── (misma estructura que ValidAttackerI)
├── _CoqProject
└── CoqMakeFile
```

### Descripcion de los modulos

**`Attacker/`**
Define el tipo `Attacker`, que representa al atacante con sus propiedades: las maquinas y usuarios que conoce, los secretos obtenidos, su vista parcial del entorno y los exploits que domina. Tambien contiene los predicados de validez del atacante (`valid_attacker_i` a `valid_attacker_iv`), que expresan distintos niveles de capacidad.

**`Machine/`**
Modela la infraestructura del sistema. `Machine.v` define los tipos fundamentales (privilegios, usuarios, servicios, cuentas). `MachineAuxFunctions.v` contiene funciones auxiliares sobre maquinas. `MachineValid.v` establece las restricciones de validez de una maquina. `MachineView.v` define vistas parciales del estado de una maquina.

**`Technique/`**
Define las tecnicas de ataque disponibles como un tipo inductivo (`Technique`) organizado segun el framework MITRE ATT&CK (movimiento lateral, acceso a credenciales, descubrimiento, escalada de privilegios). Los archivos `TechniquePreCondition.v`, `TechniquePostCondition.v` y `TechniqueOneStep.v` especifican las precondiciones, postcondiciones y la semantica de ejecucion en un paso de cada tecnica.

**`Invariant/`**
Contiene todas las pruebas de invariantes. Se organiza en tres subcarpetas:

- **`AuxLemmas/`**: Lemas auxiliares reutilizados a lo largo del proyecto, agrupados por tema (cuentas, archivos, servicios, entorno, vecinos, logica general y tacticas).
- **`AttackerCapacity/`**: Predicados de alcance y acceso del atacante, que refinan la nocion de que recursos puede comprometer.
- **`ValidAttacker/`**: Pruebas principales. Hay cuatro niveles (`ValidAttackerI` a `ValidAttackerIV`), cada uno con un archivo por tecnica de ataque y un archivo integrador (`OneStepPreservesValidAttackerX.v`). `ValidAttacker.v` en la raiz combina todos los niveles en el teorema principal: `one_step_preserves_valid_attacker`.

## Compilacion

El proyecto requiere Coq 8.18. Se recomienda gestionar la instalacion con [opam](https://opam.ocaml.org/).

### Configurar el entorno con opam

```bash
# Crear un switch con la version correcta de OCaml compatible con Coq 8.18
opam switch create coq818 4.14.2

# Activar el switch
eval $(opam env --switch=coq818)

# Agregar el repositorio de Coq
opam repo add coq-released https://coq.inria.fr/opam/released

# Instalar Coq 8.18
opam install coq.8.18.0
```

### Compilar el proyecto

Cada vez que se inicia una sesión en la terminal primero es necesario cargar el entorno de `opam` con el switch creado previamente y seleccionado.
```bash
eval $(opam env)
```

```bash
# Desde la raiz del repositorio, generar el Makefile
coq_makefile -f _CoqProject -o CoqMakeFile

# Compilar todos los archivos
make -f CoqMakeFile
```

Para compilar un archivo especifico:

```bash
make -f CoqMakeFile Invariant/ValidAttacker/ValidAttacker.vo
```

Para limpiar los archivos compilados:

```bash
make -f CoqMakeFile clean
```
