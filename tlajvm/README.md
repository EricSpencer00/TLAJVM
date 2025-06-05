# TLAJVM - TLA+ Specification Inference from Java

This project aims to automatically generate TLA+ specifications from Java code. It uses JavaParser to analyze Java source code and generate corresponding TLA+ specifications that can be model checked using TLC or Apalache.

## Project Structure

```
tlajvm/
├── src/
│   ├── main/
│   │   ├── java/
│   │   │   └── com/
│   │   │       └── tlajvm/
│   │   │           └── parser/
│   │   │               ├── AstExplorer.java
│   │   │               └── MySimpleProgram.java
│   │   └── resources/
│   │       └── logback.xml
│   └── test/
│       └── java/
│           └── com/
│               └── tlajvm/
│                   └── parser/
│                       └── AstExplorerTest.java
└── pom.xml
```

## Getting Started

### Prerequisites

- Java 17 or later
- Maven 3.6 or later
- TLA+ Toolbox (for model checking)

### Building the Project

```bash
mvn clean install
```

### Running the AST Explorer

```bash
mvn exec:java -Dexec.mainClass="com.tlajvm.parser.AstExplorer"
```

### Running Tests

```bash
mvn test
```

## Features

- Java source code parsing using JavaParser
- AST exploration and analysis
- Basic TLA+ specification generation (in progress)
- Test coverage for core functionality

## Development Status

This project is currently in the early stages of development. The following features are implemented:

- [x] Basic Java source code parsing
- [x] AST exploration and method analysis
- [ ] TLA+ specification generation
- [ ] Model checking integration

## Contributing

1. Fork the repository
2. Create a feature branch
3. Commit your changes
4. Push to the branch
5. Create a Pull Request

## License

This project is licensed under the MIT License - see the LICENSE file for details. 