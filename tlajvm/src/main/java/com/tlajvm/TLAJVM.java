package com.tlajvm;

import lombok.extern.slf4j.Slf4j;

@Slf4j
public class TLAJVM {
    public static void main(String[] args) {
        log.info("TLAJVM starting up...");
        // TODO: Implement JVM initialization
        Parse.main(args);
        log.info("TLAJVM initialized successfully");
    }
} 