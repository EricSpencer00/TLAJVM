package com.tlajvm.parser;

public class TestProgram {
    private int counter = 0;
    private boolean isRunning = true;
    private int[] values = new int[3];
    private boolean[][] flags = new boolean[3][3];

    public TestProgram() {
        for (int i = 0; i < values.length; i++) {
            values[i] = i;
            for (int j = 0; j < flags[i].length; j++) {
                flags[i][j] = (i + j) % 2 == 0;
            }
        }
    }

    public void process() {
        while (isRunning && counter < 5) {
            for (int i = 0; i < values.length; i++) {
                if (values[i] % 2 == 0 && checkFlag(i, counter % 3)) {
                    incrementCounter(i);
                } else {
                    decrementCounter(i);
                }
            }
            checkStatus();
        }
    }

    private void incrementCounter(int idx) {
        counter += values[idx];
        System.out.println("Counter incremented by " + values[idx] + ": " + counter);
    }

    private void decrementCounter(int idx) {
        counter -= values[idx];
        System.out.println("Counter decremented by " + values[idx] + ": " + counter);
    }

    private boolean checkFlag(int i, int j) {
        return flags[i][j];
    }

    private void checkStatus() {
        if (counter >= 10 || counter < 0) {
            isRunning = false;
        }
    }

    public static void main(String[] args) {
        TestProgram program = new TestProgram();
        program.process();
    }
} 