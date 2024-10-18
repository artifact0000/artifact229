# How to use these scripts

1. You can clear everything with:
```
./clean
```

2. Run:
```
./bench-prepare
```

`./bench-prepare` will:
* Call ./clean
* Build the `.s` files from `plain/`, `sslh/`, and `sslh_rsb/`
* Create directory `artifact/bench-prepared/` with:
  * the `.s` and `api.h` files, under `src/` (for `plain/`, `sslh/`, and `sslh_rsb/`);
  * the benchmarking code under `bench/` (for `plain/`, `sslh/`, and `sslh_rsb/`);
  * the `ssbd-tools/`: the script **does not** run `git submodule init && git submodule update);
  * a script to run and pack the benchmarks: `bench-prepared/bench-run`
* Then it will `tar` the directory and remove it
* Check bench-prepared.tar.bz2

The main reason why this script exists is to make life easier when benchmarking in machines without the Jasmin compiler.

3. You can send the `bench-prepared.tar.bz2` to the machine and run the benchmarks:

```
tar -xf bench-prepared.tar.bz2
cd bench-prepared/
./bench-run
```

`bench-run` will:
* create a `results.tar.bz2` with the benchmarking results.






