#!/bin/bash

# Build the project
echo "Building project..."
mvn clean package

# Run the pipeline
echo "Running Java to TLA+ pipeline..."
if [ "$1" == "--file" ] && [ -n "$2" ]; then
    # Process a single file (absolute or relative path)
    java_file="$2"
    output_dir="${3:-src/main/resources/tla-specs}"
    mvn exec:java -Dexec.mainClass="com.tlajvm.parser.JavaToTlaPipeline" -Dexec.args="$java_file $output_dir"
elif [ "$1" == "--dir" ] && [ -n "$2" ]; then
    # Process a directory (absolute or relative path)
    java_dir="$2"
    output_dir="${3:-src/main/resources/tla-specs}"
    mvn exec:java -Dexec.mainClass="com.tlajvm.parser.JavaToTlaPipeline" -Dexec.args="$java_dir $output_dir"
else
    echo "Usage: ./run-pipeline.sh --file <java-file> [output-dir]"
    echo "   or: ./run-pipeline.sh --dir <java-directory> [output-dir]"
    exit 1
fi

# Check if TLA+ Toolbox is installed
if ! command -v tla2tools.jar &> /dev/null; then
    echo "TLA+ Toolbox not found. Please install it to view the specifications."
    echo "Download from: https://lamport.azurewebsites.net/tla/toolbox.html"
fi 