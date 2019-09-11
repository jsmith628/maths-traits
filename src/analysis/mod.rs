//!
//!Traits for sets with orderings and metrics
//!
//!Traits in this module have been split into three groups:
//!* ["Ordered"](analysis::ordered) sets and related properties. This includes the
//! [archimedian property](analysis::ArchimedeanProperty) and ordered algebraic systems.
//!* Traits for [Real](analysis::Real) and [Complex](analysis::Complex) properties and representations
//!* ["Metric"](analysis::metric) properties and functions. This includes
//! [metrics](analysis::Metric), [norms](analysis::Norm), and [inner-products](analysis::InnerProductSpace)
//!
//!For ease of use, members of each module have been re-exported into this one.
//!

pub use self::ordered::*;
pub use self::real::*;
pub use self::metric::*;

pub mod ordered;
pub mod real;
pub mod metric;
