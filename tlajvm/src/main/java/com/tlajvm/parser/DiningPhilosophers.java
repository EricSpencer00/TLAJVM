package com.tlajvm.parser;

public class DiningPhilosophers {
    private boolean[] forks;  // true if fork is available
    private int[] states;     // 0: thinking, 1: hungry, 2: eating
    private int numPhilosophers;

    public DiningPhilosophers(int numPhilosophers) {
        this.numPhilosophers = numPhilosophers;
        this.forks = new boolean[numPhilosophers];
        this.states = new int[numPhilosophers];
        
        // Initialize all forks as available
        for (int i = 0; i < numPhilosophers; i++) {
            forks[i] = true;
            states[i] = 0;  // All philosophers start thinking
        }
    }

    public void philosopher(int id) {
        while (true) {
            // Think
            if (states[id] == 0) {
                states[id] = 1;  // Become hungry
            }
            // Try to eat
            else if (states[id] == 1) {
                int leftFork = id;
                int rightFork = (id + 1) % numPhilosophers;
                
                // Try to pick up forks
                if (forks[leftFork] && forks[rightFork]) {
                    forks[leftFork] = false;
                    forks[rightFork] = false;
                    states[id] = 2;  // Start eating
                }
            }
            // Finish eating
            else if (states[id] == 2) {
                int leftFork = id;
                int rightFork = (id + 1) % numPhilosophers;
                
                // Put down forks
                forks[leftFork] = true;
                forks[rightFork] = true;
                states[id] = 0;  // Back to thinking
            }
        }
    }

    public static void main(String[] args) {
        DiningPhilosophers dp = new DiningPhilosophers(3);  // 3 philosophers for simplicity
        
        // Start philosophers
        for (int i = 0; i < 3; i++) {
            final int id = i;
            new Thread(() -> dp.philosopher(id)).start();
        }
    }
} 