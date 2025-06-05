#!/bin/bash

# Build the project
echo "Building project..."
mvn clean package

# Run the pipeline
echo "Running Java to TLA+ pipeline..."
if [ "$1" == "--file" ] && [ -n "$2" ]; then
    # Process a single file
    mvn exec:java -Dexec.mainClass="com.tlajvm.parser.JavaToTlaPipeline" -Dexec.args="src/main/java/com/tlajvm/parser/$2 src/main/resources/tla-specs"
elif [ "$1" == "--dir" ] && [ -n "$2" ]; then
    # Process a directory
    mvn exec:java -Dexec.mainClass="com.tlajvm.parser.JavaToTlaPipeline" -Dexec.args="$2 src/main/resources/tla-specs"
else
    echo "Usage: ./run-pipeline.sh --file <java-file>"
    echo "   or: ./run-pipeline.sh --dir <java-directory>"
    exit 1
fi

# Check if TLA+ Toolbox is installed
if ! command -v tla2tools.jar &> /dev/null; then
    echo "TLA+ Toolbox not found. Please install it to view the specifications."
    echo "Download from: https://lamport.azurewebsites.net/tla/toolbox.html"
fi 