package Generater.MUTMutation;

import spoon.reflect.code.CtAbstractInvocation;
import spoon.reflect.declaration.CtElement;
import spoon.reflect.reference.CtTypeReference;
import utils.Pair;

import java.util.*;
import java.util.stream.Collectors;
import java.util.function.Function;

/**
 * Analyzer class to review CandidatePool types and MUTInput combination statistics
 * for understanding performance bottlenecks and optimization opportunities.
 */
public class CombinationAnalyzer {

    public static class CombinationStats {
        public long totalCombinations;
        public int parametersCount;
        public Map<Integer, Integer> positionPoolSizes = new HashMap<>();
        public List<Integer> poolSizes = new ArrayList<>();
        public boolean isExplosive; // > 10M combinations
        public String methodSignature;
        
        @Override
        public String toString() {
            return String.format("Method: %s | Params: %d | Total Combinations: %,d%s | Pool Sizes: %s",
                methodSignature, parametersCount, totalCombinations, 
                isExplosive ? " [EXPLOSIVE!]" : "", poolSizes);
        }
    }

    public static class PoolAnalysisReport {
        public int totalUniqueTypes;
        public int totalVariables;
        public int totalLiterals;
        public int totalMUTs;
        public long totalPossibleCombinations;
        public List<CombinationStats> mutStats = new ArrayList<>();
        public Map<String, Integer> typeDistribution = new HashMap<>();
        public List<String> mostPopulousTypes = new ArrayList<>();
        public List<String> explosiveMUTs = new ArrayList<>();
        public double averageCombinations;
        public double medianCombinations;
        public long minCombinations;
        public long maxCombinations;
        
        public void printSummary() {
            String separator = "================================================================================";
            System.out.println("\n" + separator);
            System.out.println("           COMBINATION EXPLOSION ANALYSIS REPORT");
            System.out.println(separator);
            
            // Overall Statistics - Focus on processed MUTs only
            System.out.println("\n📊 PROCESSED MUTs STATISTICS:");
            System.out.printf("   • Total Processed MUTs: %,d\n", totalMUTs);
            System.out.printf("   • Theoretical Max Combinations: %,d\n", totalPossibleCombinations);

            // List all MUT signatures
            System.out.println("\n📋 ALL MUT SIGNATURES:");
            List<String> sortedSignatures = mutStats.stream()
                .map(s -> s.methodSignature)
                .sorted()
                .collect(Collectors.toList());
            for (int i = 0; i < sortedSignatures.size(); i++) {
                System.out.printf("   %3d. %s\n", i + 1, sortedSignatures.get(i));
            }

            // MUT Combination Analysis
            System.out.println("\n⚡ MUT COMBINATION EXPLOSION ANALYSIS:");
            long explosiveCount = mutStats.stream().mapToLong(s -> s.isExplosive ? 1 : 0).sum();
            System.out.printf("   • MUTs with >10M combinations: %,d (%.1f%%)\n", 
                explosiveCount, (explosiveCount * 100.0) / totalMUTs);
            
            // Average and statistical analysis
            System.out.println("\n📊 COMBINATION STATISTICS:");
            System.out.printf("   • Average combinations per MUT: %,.0f\n", averageCombinations);
            System.out.printf("   • Median combinations per MUT: %,.0f\n", medianCombinations);
            System.out.printf("   • Min combinations: %,d\n", minCombinations);
            System.out.printf("   • Max combinations: %,d\n", maxCombinations);
            
            // Calculate standard deviation
            double variance = 0.0;
            for (CombinationStats stats : mutStats) {
                variance += Math.pow(stats.totalCombinations - averageCombinations, 2);
            }
            double standardDeviation = Math.sqrt(variance / mutStats.size());
            System.out.printf("   • Standard deviation: %,.0f\n", standardDeviation);
            
            // Show distribution percentiles
            List<Long> sortedCombinations = new ArrayList<>();
            for (CombinationStats stats : mutStats) {
                sortedCombinations.add(stats.totalCombinations);
            }
            Collections.sort(sortedCombinations);
            
            int size = sortedCombinations.size();
            long p25 = sortedCombinations.get((int)(size * 0.25));
            long p75 = sortedCombinations.get((int)(size * 0.75));
            long p95 = sortedCombinations.get((int)(size * 0.95));
            
            System.out.printf("   • 25th percentile: %,d\n", p25);
            System.out.printf("   • 75th percentile: %,d\n", p75);
            System.out.printf("   • 95th percentile: %,d\n", p95);
            
            // Top 10 Most Explosive MUTs
            System.out.println("\n💥 TOP 10 MOST EXPLOSIVE MUTs:");
            List<CombinationStats> topExplosive = mutStats.stream()
                .sorted((a, b) -> Long.compare(b.totalCombinations, a.totalCombinations))
                .limit(10)
                .collect(Collectors.toList());
            for (CombinationStats stat : topExplosive) {
                System.out.printf("   • %s\n", stat.toString());
            }
            
            // Distribution by combination count
            System.out.println("\n📈 COMBINATION COUNT DISTRIBUTION:");
            Map<String, Long> ranges = new HashMap<>();
            ranges.put("1-100", mutStats.stream().filter(s -> s.totalCombinations <= 100).count());
            ranges.put("101-1K", mutStats.stream().filter(s -> s.totalCombinations > 100 && s.totalCombinations <= 1000).count());
            ranges.put("1K-10K", mutStats.stream().filter(s -> s.totalCombinations > 1000 && s.totalCombinations <= 10000).count());
            ranges.put("10K-100K", mutStats.stream().filter(s -> s.totalCombinations > 10000 && s.totalCombinations <= 100000).count());
            ranges.put("100K-1M", mutStats.stream().filter(s -> s.totalCombinations > 100000 && s.totalCombinations <= 1000000).count());
            ranges.put("1M-10M", mutStats.stream().filter(s -> s.totalCombinations > 1000000 && s.totalCombinations <= 10000000).count());
            ranges.put(">10M", mutStats.stream().filter(s -> s.totalCombinations > 10000000).count());
            
            for (Map.Entry<String, Long> entry : ranges.entrySet()) {
                System.out.printf("   • %s combinations: %,d MUTs\n", entry.getKey(), entry.getValue());
            }
            
            // Recommendations
            System.out.println("\n🎯 OPTIMIZATION RECOMMENDATIONS:");
            if (explosiveCount > 0) {
                System.out.println("   • CRITICAL: Implement input pool pruning for explosive MUTs");
                System.out.printf("   • URGENT: %,d MUTs need immediate attention\n", explosiveCount);
            }
            if (totalVariables > 1000) {
                System.out.println("   • HIGH: Consider variable deduplication strategies");
            }
            if (typeDistribution.size() > 100) {
                System.out.println("   • MEDIUM: Implement type-based caching optimization");
            }
            
            System.out.println(separator);
        }
    }

    /**
     * Comprehensive analysis of CandidatePool and MUT combinations
     */
    public static PoolAnalysisReport analyzeCombinationExplosion(Set<MUTInput> mutInputs) {
        PoolAnalysisReport report = new PoolAnalysisReport();
        
        System.out.println("🔍 Starting Combination Explosion Analysis...");
        
        // 1. Analyze CandidatePool contents
        analyzeCandidatePool(report);
        
        // 2. Analyze MUT combinations
        analyzeMUTInputs(mutInputs, report);
        
        // 3. Calculate totals and generate insights
        generateInsights(report);
        
        System.out.println("✅ Analysis Complete!\n");
        
        return report;
    }

    private static void analyzeCandidatePool(PoolAnalysisReport report) {
        // Skip CandidatePool analysis - will be set after MUT analysis
        report.totalVariables = 0;
        report.totalLiterals = 0;
        report.totalUniqueTypes = 0;
    }

    private static void analyzeMUTInputs(Set<MUTInput> mutInputs, PoolAnalysisReport report) {
        System.out.printf("   Analyzing %,d MUT inputs...\n", mutInputs.size());
        
        long totalCombinations = 0;
        
        for (MUTInput mutInput : mutInputs) {
            CombinationStats stats = calculateCombinationStats(mutInput);
            report.mutStats.add(stats);
            
            totalCombinations += stats.totalCombinations;
            
            if (stats.isExplosive) {
                report.explosiveMUTs.add(stats.methodSignature);
            }
        }
        
        report.totalPossibleCombinations = totalCombinations;
        report.totalMUTs = mutInputs.size(); // Set the correct count here
    }

    private static CombinationStats calculateCombinationStats(MUTInput mutInput) {
        CombinationStats stats = new CombinationStats();
        
        stats.methodSignature = mutInput.getMethodSignature();
        stats.parametersCount = mutInput.getInputs().size();
        
        // Calculate total combinations (cartesian product)
        long totalCombinations = 1;
        for (Map.Entry<Integer, List<Input>> entry : mutInput.getInputs().entrySet()) {
            int poolSize = entry.getValue().size();
            stats.positionPoolSizes.put(entry.getKey(), poolSize);
            stats.poolSizes.add(poolSize);
            
            totalCombinations *= poolSize;
            
            // Prevent overflow
            if (totalCombinations > 1_000_000_000L) {
                totalCombinations = 1_000_000_000L;
                break;
            }
        }
        
        stats.totalCombinations = totalCombinations;
        stats.isExplosive = totalCombinations > 10_000_000; // 10M threshold
        
        return stats;
    }

    private static void generateInsights(PoolAnalysisReport report) {
        if (report.mutStats.isEmpty()) {
            report.averageCombinations = 0.0;
            report.medianCombinations = 0.0;
            report.minCombinations = 0;
            report.maxCombinations = 0;
            return;
        }
        
        // Calculate average combinations
        long totalCombinations = 0;
        long minCombinations = Long.MAX_VALUE;
        long maxCombinations = Long.MIN_VALUE;
        
        for (CombinationStats stats : report.mutStats) {
            totalCombinations += stats.totalCombinations;
            minCombinations = Math.min(minCombinations, stats.totalCombinations);
            maxCombinations = Math.max(maxCombinations, stats.totalCombinations);
        }
        
        report.averageCombinations = (double) totalCombinations / report.mutStats.size();
        report.minCombinations = minCombinations;
        report.maxCombinations = maxCombinations;
        
        // Calculate median combinations
        List<Long> sortedCombinations = new ArrayList<>();
        for (CombinationStats stats : report.mutStats) {
            sortedCombinations.add(stats.totalCombinations);
        }
        Collections.sort(sortedCombinations);
        
        int size = sortedCombinations.size();
        if (size % 2 == 0) {
            report.medianCombinations = (sortedCombinations.get(size/2 - 1) + sortedCombinations.get(size/2)) / 2.0;
        } else {
            report.medianCombinations = sortedCombinations.get(size/2);
        }
        
        System.out.printf("   Generated insights for %,d MUTs\n", report.mutStats.size());
        System.out.printf("   Average combinations: %,.0f | Median: %,.0f | Range: %,d - %,d\n", 
            report.averageCombinations, report.medianCombinations, 
            report.minCombinations, report.maxCombinations);
    }

    /**
     * Quick method to print just the average combinations statistics
     */
    public static void printAverageStats(Set<MUTInput> mutInputs) {
        if (mutInputs.isEmpty()) {
            System.out.println("📊 No MUTs available for analysis.");
            return;
        }
        
        System.out.println("\n📊 AVERAGE COMBINATIONS ANALYSIS:");
        String separator = "----------------------------------------";
        System.out.println(separator);
        
        long totalCombinations = 0;
        long minCombinations = Long.MAX_VALUE;
        long maxCombinations = Long.MIN_VALUE;
        List<Long> allCombinations = new ArrayList<>();
        
        for (MUTInput mutInput : mutInputs) {
            CombinationStats stats = calculateCombinationStats(mutInput);
            totalCombinations += stats.totalCombinations;
            minCombinations = Math.min(minCombinations, stats.totalCombinations);
            maxCombinations = Math.max(maxCombinations, stats.totalCombinations);
            allCombinations.add(stats.totalCombinations);
        }
        
        double average = (double) totalCombinations / mutInputs.size();
        
        // Calculate median
        Collections.sort(allCombinations);
        double median;
        int size = allCombinations.size();
        if (size % 2 == 0) {
            median = (allCombinations.get(size/2 - 1) + allCombinations.get(size/2)) / 2.0;
        } else {
            median = allCombinations.get(size/2);
        }
        
        System.out.printf("Total MUTs analyzed: %,d\n", mutInputs.size());
        System.out.printf("Average combinations per MUT: %,.0f\n", average);
        System.out.printf("Median combinations per MUT: %,.0f\n", median);
        System.out.printf("Min combinations: %,d\n", minCombinations);
        System.out.printf("Max combinations: %,d\n", maxCombinations);
        
        // Count explosive MUTs
        long explosiveCount = allCombinations.stream().mapToLong(c -> c > 10_000_000 ? 1 : 0).sum();
        System.out.printf("Explosive MUTs (>10M): %,d (%.1f%%)\n", 
            explosiveCount, (explosiveCount * 100.0) / mutInputs.size());
        
        System.out.println(separator);
    }

    /**
     * Quick method to print just the explosive MUTs
     */
    public static void printExplosiveMUTs(Set<MUTInput> mutInputs) {
        System.out.println("\n💥 EXPLOSIVE MUTs (>10M combinations):");
        String separator = "--------------------------------------------------------------------------------";
        System.out.println(separator);
        
        List<CombinationStats> explosiveMUTs = mutInputs.stream()
            .map(mut -> calculateCombinationStats(mut))
            .filter(stats -> stats.isExplosive)
            .sorted((a, b) -> Long.compare(b.totalCombinations, a.totalCombinations))
            .collect(Collectors.toList());
        
        if (explosiveMUTs.isEmpty()) {
            System.out.println("✅ No explosive MUTs found!");
        } else {
            System.out.printf("⚠️  Found %,d explosive MUTs:\n\n", explosiveMUTs.size());
            for (CombinationStats stats : explosiveMUTs) {
                System.out.println("   " + stats.toString());
            }
        }
        
        System.out.println(separator);
    }

    /**
     * Print detailed breakdown for a specific MUT
     */
    public static void printMUTDetails(MUTInput mutInput) {
        System.out.println("\n🔍 DETAILED MUT ANALYSIS:");
        String separator = "------------------------------------------------------------";
        System.out.println(separator);
        
        CombinationStats stats = calculateCombinationStats(mutInput);
        System.out.println("Method: " + stats.methodSignature);
        System.out.printf("Total Parameters: %d\n", stats.parametersCount);
        System.out.printf("Total Combinations: %,d%s\n", 
            stats.totalCombinations, stats.isExplosive ? " [EXPLOSIVE!]" : "");
        
        System.out.println("\nParameter Pool Sizes:");
        for (Map.Entry<Integer, Integer> entry : stats.positionPoolSizes.entrySet()) {
            System.out.printf("   Position %d: %,d candidates\n", 
                entry.getKey(), entry.getValue());
        }
        
        // Show actual inputs for first few positions (sample)
        System.out.println("\nSample Inputs (first 3 per position):");
        for (Map.Entry<Integer, List<Input>> entry : mutInput.getInputs().entrySet()) {
            System.out.printf("   Position %d:\n", entry.getKey());
            List<Input> sampleInputs = entry.getValue().stream().limit(3).collect(Collectors.toList());
            for (Input input : sampleInputs) {
                String inputStr = input.toString();
                String displayStr = inputStr.length() > 100 ? inputStr.substring(0, 97) + "..." : inputStr;
                System.out.printf("     • %s\n", displayStr);
            }
            
            if (entry.getValue().size() > 3) {
                System.out.printf("     ... and %,d more\n", entry.getValue().size() - 3);
            }
        }
        
        System.out.println(separator);
    }
}