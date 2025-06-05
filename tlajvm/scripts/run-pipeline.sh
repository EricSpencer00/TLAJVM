#!/bin/bash

# run-pipeline.sh
# This script builds the project and runs the Java-to-TLA+ pipeline.
# It accepts a Java file or directory as input and generates TLA+ specifications.

# Exit on error
set -e

# Build the project
echo "Building project..."
mvn clean package

# Parse command-line arguments
if [ "$1" == "--file" ] && [ -n "$2" ]; then
    # Process a single file
    java_file="$2"
    output_dir="${3:-src/main/resources/tla-specs}"
    echo "Running Java to TLA+ pipeline on file: $java_file"
    mvn exec:java -Dexec.mainClass="com.tlajvm.parser.JavaToTlaPipeline" -Dexec.args="$java_file $output_dir"
elif [ "$1" == "--dir" ] && [ -n "$2" ]; then
    # Process a directory
    java_dir="$2"
    output_dir="${3:-src/main/resources/tla-specs}"
    echo "Running Java to TLA+ pipeline on directory: $java_dir"
    mvn exec:java -Dexec.mainClass="com.tlajvm.parser.JavaToTlaPipeline" -Dexec.args="$java_dir $output_dir"
else
    echo "Usage: $0 --file <java-file> [output-dir]"
    echo "   or: $0 --dir <java-directory> [output-dir]"
    exit 1
fi

# Check if TLA+ Toolbox is installed
if ! command -v tla2tools &> /dev/null; then
    echo "TLA+ Toolbox not found. Please install it to view the specifications."
    echo "Download from: https://lamport.azurewebsites.net/tla/toolbox.html"
fi 