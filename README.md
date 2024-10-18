# Protecting cryptographic code against Spectre-RSB

This is the artifact for the paper `Protecting cryptographic code against Spectre-RSB`.

## Contents

This artifact contains the following directories:

  - `jasmin`, a contribution of this work: an improved version of the Jasmin compiler
  - `sslh_rsb`, a contribution of this work, a fully protected version of libjade
  - `tables`: in `tables/main.pdf` you can find results tables. The raw benchmark results are
     included under `tables/data`.

  - `plain`: libjade with no spectre protections, for comparison purposes.
  - `sslh`: libjade with v1 protections from "Typing high-speed cryptography against spectre v1",
      for comparison purposes.
  - `ssbd-tools`: "Tools to exercise the Linux kernel mitigation for CVE-2018-3639 (aka Variant 4)
      using the Speculative Store Bypass Disable (SSBD) feature of x86 processors", description from
      https://github.com/tyhicks/ssbd-tools
  - `scripts`: bash scripts to perform several utility tasks such as preparing or running the benchmarks.
  - `formalization`, a formalization in Coq of the source and target speculative semantics, the type system, the compilation using jump table for return, and of the theorem 1 and 2 of the paper. 

## Contributions

The main contributions in this artifact are:

  - Jasmin SCT type checker
  - The formalization of the languages and a formal proof that our compilation scheme for return generate SCT target programs (under the assumption that program are well typed, theorem 2).

  - High-Assurance cryptographic implementations resistant to "all known Spectre variants"

## Building Jasmin

The recommended way to build the modified Jasmin compiler is using nix; for installation
instructions of nix, see https://nixos.org/download.html
To build Jasmin using nix, run in the `jasmin/` directory, the command

    nix-shell --run 'make'

Once the compiler is built, it is advised to put it in your path or to run, in this directory:

    export JASMIN=$PWD/jasmin/compiler/jasminc

**Alternatively**, you can use the provided docker image to setup a configured environment with the Jasmin compiler installed:
```
docker build -t asplos-rsbsecure:latest -f Dockerfile .
docker run -it asplos-rsbsecure bash
```
And continuing with the reading. This process should take around 10 minutes.

## Building the formalization
The recommended way to build the modified Jasmin compiler is using nix; for installation
instructions of nix, see https://nixos.org/download.html

To build the formalization:
   cd formalization
   $ USER=asplos source $HOME/.nix-profile/etc/profile.d/nix.sh
   $ nix-shell
   $ dune build

The Coq files are in the repository formalization/src
  syntax.v: 
    Syntax of the source language.

  linear.v: 
    Syntax and semantics of the target language.

  semantics.v: 
    Semantics of the source language.

  typesystem.v: 
    Definition of the type system.

  typesystem_facts.v: 
    Lemmas on the type systems.

  security.v: 
    Definition of SCT and low equivalences

  linearization.v: 
    Compilation scheme, i.e. definition of the return table insertion.  

  results.v: 
    Agregation of the three main lemmas
    - soundness of the source type system (proved security_facts.v, Theorem 1)
    - preservation of leakage             (proved linearization_facts.v, Theorem 2)
    - typable machine don't get stuck     (proved in both_step.v)

  examples.v: 
    Examples of type derivation of programs in the paper. 		

  Auxiliary files:
    var.v
    semantics_facts.v	
    syntax_facts.v
    notations.v
    utils.v
    utils_facts.v
    examples_utils.v

## Building and checking libjade

### To build `sslh_rsb/src/libjade.a`

```
make -C sslh_rsb/src -j$(nproc) libjade.a
```
Note: you can omit `-j$(nproc)` if you wish to not use more than one job.

You can now use the library, `sslh_rsb/src/libjade.a`, and the corresponding header file,
`sslh_rsb/src/libjade.h` in your projects.


After libjade is compiled, you can still find all the compiled assembly files (for instance, to use
them individually) by running:
```
find sslh_rsb/ -name "*.s"
```
Note: for the object files, replace `*.s` by `*.o`.


Each assembly file has a corresponding header file, `include/api.h`. These can be found with:
```
find sslh_rsb/ -name "api.h"
```

### To check security:
```
make -C sslh_rsb/src -j$(nproc) CI=1 sct
make -C sslh_rsb/src -j$(nproc) CI=1 reporter_sct
```

The first command runs the SCT checker on the source code and stores the logs into `*.sct` files.
These can be found with `find sslh_rsb/ -name "*.sct"`.

The second command reports about the status of the security checking: you should observe all
implementations tagged as "OK". Note, if you run the second command twice, on the second time
it will show nothing: the default behavior is to delete all OK files for the developer to
focus on the ERRor files. To avoid this behavior, and always show the OK files, you can add
`CICL=0` to the command to prevent this cleaning from happening, 
`make -C sslh_rsb/src -j$(nproc) CI=1 CICL=0 reporter_sct`.

As an exercise, try to remove an `#update_after_call` annotation. These can be easily found
by running `grep -nr "#update_after_call"`. After poisoning a given file, run the first and
second command again to observe an error. You can also inspect the corresponding `*.sct` file,
that is located next to the corresponding `*.jazz` or `*.s` assembly file, to look for the
details that caused the failure. If you followed this exercise, don't forget to restore the
code to its original state.

### To perform a complete cleanup:
```
make -C sslh_rsb/src -j$(nproc) CI=1 distclean
```


## Benchmarking

### Preparation
Before running the benchmarks, ensure that the machine is configured for this purpose to get
stable results. Run:
```
./scripts/bench-prepare
```

`./scripts/bench-prepare` creates a directory named `bench-prepared` (and a corresponding
`bench-prepared.tar.bz2` if you wish to easily send this file into a machine that does not
have the Jasmin compiler configured and run the benchmarks there).

Note: if you are in a docker container but would like to run the benchmarks on the host
machine, or some other machine, you can copy the `bench-prepared` directory with:
```
docker cp unruffled_curran:/home/asplos/bench-prepared bench-prepared-in-docker
```
Where `unruffled_curran` should be replaced by the container name, which can be obtained by
running `docker ps`.


### Running a simple benchmark first

To run, for instance, the Kyber768 benchmark, let's say, 11 times, and each time measuring
10000 executions, and filter by `keypair` using `grep` and sorting by the number of cycles
using `sort`, run:
```
cd bench-prepared/sslh/bench
make bin/crypto_kem/kyber/kyber768/amd64/avx2/bench DEFINE="-DRUNS=11 -DTIMINGS=10000"
bin/crypto_kem/kyber/kyber768/amd64/avx2/bench - | grep keypair | sort -t, -k1
```
You can try the same for `enc` or `dec`.


### Running the complete benchmark setup
```
cd bench-prepared/
./bench-run
```

After changing directories with `cd bench-prepared/`, or with `cd bench-prepared-in-docker` if
you switched machines in the meantime, you can run the benchmarks with `./bench-run`: it can
take up to one hour.

To include the benchmark results into the `tables/main.pdf` file (where CPU is the name of your CPU):
```
cp -r results/ ../tables/data/raw/CPU
make -C ../tables/ all
```
Note: the chosen name will be used in a `\label{(...)CPU(...)}` LaTeX command for the generated table,
characters restrictions must be considered.


The `main.pdf` should now contain the new tables.
This docker image does not contain LaTeX, you will not be able to compile
`tables/main.pdf` without installing it.

