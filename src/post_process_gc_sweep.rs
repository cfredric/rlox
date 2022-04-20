use std::collections::HashMap;

use crate::heap::Ptr;

pub(crate) struct GcSweepData {
    pub(crate) pointer_mapping: HashMap<Ptr, Ptr>,
}

pub(crate) trait PostProcessGcSweep {
    fn process(&mut self, sweep_data: &GcSweepData);
}

impl PostProcessGcSweep for () {
    fn process(&mut self, _: &GcSweepData) {}
}

impl<T: PostProcessGcSweep> PostProcessGcSweep for Vec<T> {
    fn process(&mut self, sweep_data: &GcSweepData) {
        for e in self {
            e.process(sweep_data);
        }
    }
}

impl<K, V: PostProcessGcSweep> PostProcessGcSweep for HashMap<K, V> {
    fn process(&mut self, sweep_data: &GcSweepData) {
        for v in self.values_mut() {
            v.process(sweep_data);
        }
    }
}

impl<T: PostProcessGcSweep> PostProcessGcSweep for Option<T> {
    fn process(&mut self, sweep_data: &GcSweepData) {
        if let Some(t) = self {
            t.process(sweep_data);
        }
    }
}

impl<T: PostProcessGcSweep> PostProcessGcSweep for &mut T {
    fn process(&mut self, sweep_data: &GcSweepData) {
        (*self).process(sweep_data);
    }
}

impl<T: PostProcessGcSweep, U: PostProcessGcSweep> PostProcessGcSweep for (T, U) {
    fn process(&mut self, sweep_data: &GcSweepData) {
        self.0.process(sweep_data);
        self.1.process(sweep_data);
    }
}
