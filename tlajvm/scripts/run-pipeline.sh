#!/bin/bash

# Default values
JAVA_SOURCE_DIR="src/main/java/com/tlajvm/parser"
TLA_OUTPUT_DIR="src/main/resources/tla-specs"
JAVA_FILE=""

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --source-dir)
            JAVA_SOURCE_DIR="$2"
            shift 2
            ;;
        --output-dir)
            TLA_OUTPUT_DIR="$2"
            shift 2
            ;;
        --file)
            JAVA_FILE="$2"
            shift 2
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Build the project
echo "Building project..."
mvn clean package

# Run the pipeline
echo "Running Java to TLA+ pipeline..."
if [ -z "$JAVA_FILE" ]; then
    # Process entire directory
    mvn exec:java -Dexec.mainClass="com.tlajvm.pipeline.JavaToTlaPipeline" \
        -Dexec.args="$JAVA_SOURCE_DIR $TLA_OUTPUT_DIR"
else
    # Process single file
    mvn exec:java -Dexec.mainClass="com.tlajvm.pipeline.JavaToTlaPipeline" \
        -Dexec.args="$JAVA_SOURCE_DIR $TLA_OUTPUT_DIR $JAVA_FILE"
fi

# Check if TLA+ Toolbox is installed
if command -v tla-toolbox &> /dev/null; then
    echo "TLA+ Toolbox found. Opening generated specifications..."
    for tla_file in "$TLA_OUTPUT_DIR"/*.tla; do
        if [ -f "$tla_file" ]; then
            tla-toolbox "$tla_file" &
        fi
    done
else
    echo "TLA+ Toolbox not found. Please install it to view the specifications."
    echo "Download from: https://lamport.azurewebsites.net/tla/toolbox.html"
fi 