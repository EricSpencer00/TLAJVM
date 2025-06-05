package com.tlajvm.parser;

public class DeadlockExample {
    private boolean resource1Locked = false;
    private boolean resource2Locked = false;
    private int process1State = 0;
    private int process2State = 0;

    public void process1() {
        while (true) {
            if (process1State == 0) {
                // Try to acquire resource1
                if (!resource1Locked) {
                    resource1Locked = true;
                    process1State = 1;
                }
            } else if (process1State == 1) {
                // Try to acquire resource2
                if (!resource2Locked) {
                    resource2Locked = true;
                    process1State = 2;
                }
            } else if (process1State == 2) {
                // Release resources
                resource1Locked = false;
                resource2Locked = false;
                process1State = 0;
            }
        }
    }

    public void process2() {
        while (true) {
            if (process2State == 0) {
                // Try to acquire resource2 (different order than process1)
                if (!resource2Locked) {
                    resource2Locked = true;
                    process2State = 1;
                }
            } else if (process2State == 1) {
                // Try to acquire resource1
                if (!resource1Locked) {
                    resource1Locked = true;
                    process2State = 2;
                }
            } else if (process2State == 2) {
                // Release resources
                resource1Locked = false;
                resource2Locked = false;
                process2State = 0;
            }
        }
    }

    public static void main(String[] args) {
        DeadlockExample example = new DeadlockExample();
        // Start both processes
        new Thread(() -> example.process1()).start();
        new Thread(() -> example.process2()).start();
    }
} 