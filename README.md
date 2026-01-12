# quirrel_static_analyzer

**Static Analysis for Quirrel is now built-in!**

The standalone `quirrel_static_analyzer` project has been deprecated. Static analysis functionality has been fully integrated directly into the Quirrel language implementation.

If you'd like to use the static analyzer, please refer to the main Quirrel repository: https://github.com/GaijinEntertainment/quirrel

To get started:
1. Build the `sq` command-line tool from the Quirrel repository.
2. Run it with the `--sa` flag to enable static analysis:

```sh
sq --sa your_script.nut
```

All future development and improvements to the static analyzer will happen within the main Quirrel codebase.
