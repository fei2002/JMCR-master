package edu.tamu.aser.scheduling.strategy;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.SortedSet;

import edu.tamu.aser.instrumentation.MCRProperties;

/**
 * Reproduces a given schedule.
 */
public class ReproScheduleStrategy extends SchedulingStrategy {


    @Override
    public void startingExploration() {

    }

    @Override
    public void startingScheduleExecution() {

    }

    @Override
    public void completedScheduleExecution() {

    }

    @Override
    public boolean canExecuteMoreSchedules() {
        return false;
    }

    @Override
    public Object choose(SortedSet<?> objectChoices, ChoiceType choiceType) {
        return null;
    }

    @Override
    public List<Integer> getChoicesMadeDuringThisSchedule() {
        return Collections.emptyList();
    }
}
