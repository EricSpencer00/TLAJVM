package com.tlajvm.pipeline;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.tlajvm.parser.TlaSpecGenerator;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.FileInputStream;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

public class JavaToTlaPipeline {
    private static final Logger log = LoggerFactory.getLogger(JavaToTlaPipeline.class);
    private final Path javaSourceDir;
    private final Path tlaOutputDir;
    private final List<String> processedFiles = new ArrayList<>();

    public JavaToTlaPipeline(String javaSourceDir, String tlaOutputDir) {
        this.javaSourceDir = Paths.get(javaSourceDir);
        this.tlaOutputDir = Paths.get(tlaOutputDir);
    }

    public void processJavaFile(String javaFileName) {
        try {
            // Ensure output directory exists
            Files.createDirectories(tlaOutputDir);

            // Construct paths
            Path javaFilePath = javaSourceDir.resolve(javaFileName);
            String tlaFileName = javaFileName.replace(".java", ".tla");
            Path tlaFilePath = tlaOutputDir.resolve(tlaFileName);

            log.info("Processing Java file: {}", javaFilePath);
            
            // Parse Java file
            try (FileInputStream in = new FileInputStream(javaFilePath.toFile())) {
                CompilationUnit cu = StaticJavaParser.parse(in);
                
                // Generate TLA+ specification
                TlaSpecGenerator generator = new TlaSpecGenerator();
                generator.generateSpec(cu, tlaFilePath);
                
                log.info("Generated TLA+ specification: {}", tlaFilePath);
                processedFiles.add(tlaFileName);
            }
        } catch (IOException e) {
            log.error("Error processing file {}: {}", javaFileName, e.getMessage());
        }
    }

    public void processDirectory() {
        try {
            Files.walk(javaSourceDir)
                .filter(path -> path.toString().endsWith(".java"))
                .forEach(path -> {
                    String relativePath = javaSourceDir.relativize(path).toString();
                    processJavaFile(relativePath);
                });
        } catch (IOException e) {
            log.error("Error processing directory: {}", e.getMessage());
        }
    }

    public List<String> getProcessedFiles() {
        return new ArrayList<>(processedFiles);
    }

    public static void main(String[] args) {
        if (args.length < 2) {
            System.out.println("Usage: JavaToTlaPipeline <java-source-dir> <tla-output-dir> [java-file]");
            System.exit(1);
        }

        String javaSourceDir = args[0];
        String tlaOutputDir = args[1];
        
        JavaToTlaPipeline pipeline = new JavaToTlaPipeline(javaSourceDir, tlaOutputDir);
        
        if (args.length > 2) {
            // Process single file
            pipeline.processJavaFile(args[2]);
        } else {
            // Process entire directory
            pipeline.processDirectory();
        }

        // Print summary
        System.out.println("\nProcessed files:");
        pipeline.getProcessedFiles().forEach(System.out::println);
    }
} 