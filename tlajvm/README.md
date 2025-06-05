# TLAJVM: Java to TLA+ Specification Generator

## Overview
TLAJVM is a tool for automatically generating TLA+ specifications from arbitrary Java source files. It is designed to be fully generic and dynamic: **no hardcoded logic, no special cases, and no example-specific handling**. The pipeline processes any Java file or directory and produces a corresponding TLA+ specification.

## How It Works
- Uses JavaParser to parse Java source files.
- Traverses the AST to extract variables, assignments, control flow, and method calls.
- Generates TLA+ modules, variables, Init, and Next predicates based on the Java program structure.
- All output is written to the specified output directory (default: `src/main/resources/tla-specs/`).

## Usage

### 1. Build the Project
```sh
mvn clean package
```

### 2. Run the Pipeline
To generate a TLA+ specification for a single Java file:
```sh
./scripts/run-pipeline.sh --file /path/to/YourJavaFile.java
```

To generate TLA+ specifications for all Java files in a directory:
```sh
./scripts/run-pipeline.sh --dir /path/to/YourJavaDirectory
```

You can optionally specify a custom output directory:
```sh
./scripts/run-pipeline.sh --file /path/to/YourJavaFile.java /custom/output/dir
```

### 3. View the Output
All generated TLA+ files will appear in the output directory you specify (default: `src/main/resources/tla-specs/`).

## Project Structure
- `src/main/java/com/tlajvm/parser/JavaToTlaPipeline.java`: Main entry point for the pipeline.
- `src/main/java/com/tlajvm/parser/TlaSpecGenerator.java`: Generic Java-to-TLA+ translation logic.
- `scripts/run-pipeline.sh`: Script to build and run the pipeline.
- `src/main/resources/tla-specs/`: Default output directory for TLA+ specifications.

## What This Project Does **NOT** Do
- No hardcoded logic for any specific Java program, variable, or method.
- No special-case handling for examples like Dining Philosophers, Deadlock, etc.
- No demo/test code for direct TLA+ generation outside the pipeline.

## Contributing
Contributions are welcome! Please ensure all code is generic and does not introduce any hardcoded or special-case logic.

## License
MIT 