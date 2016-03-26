#include "Geometry.hpp"
#include "ClipperUtils.hpp"
#include "ExPolygon.hpp"
#include "Line.hpp"
#include "PolylineCollection.hpp"
#include "clipper.hpp"
#include <algorithm>
#include <cmath>
#include <list>
#include <map>
#include <set>
#include <stack>
#include <vector>
#include <assert.h>

// Property map is used heavily by the boost::graph library for addressing vertex & edge properties.
#include <boost/property_map/property_map.hpp>
// For representing the distance matrix between graph vertices. This is the result of calling boost::johnson_all_pairs_shortest()
#include <boost/multi_array.hpp>
// The graph definition.
#include <boost/graph/adjacency_list.hpp>
// Detect connected components of a graph.
#include <boost/graph/connected_components.hpp>
#include <boost/graph/graph_traits.hpp>
// Find distances between all pairs of vertices using a Dijkstra algorithm executed for each vertex as a source.
#include <boost/graph/johnson_all_pairs_shortest.hpp>

#ifdef SLIC3R_DEBUG
#include "SVG.hpp"
#include <boost/graph/graphviz.hpp>
#endif

#ifdef SLIC3R_DEBUG
namespace boost { namespace polygon {

// The following code for the visualization of the boost Voronoi diagram is based on:
//
// Boost.Polygon library voronoi_graphic_utils.hpp header file
//          Copyright Andrii Sydorchuk 2010-2012.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)
template <typename CT>
class voronoi_visual_utils {
 public:
  // Discretize parabolic Voronoi edge.
  // Parabolic Voronoi edges are always formed by one point and one segment
  // from the initial input set.
  //
  // Args:
  //   point: input point.
  //   segment: input segment.
  //   max_dist: maximum discretization distance.
  //   discretization: point discretization of the given Voronoi edge.
  //
  // Template arguments:
  //   InCT: coordinate type of the input geometries (usually integer).
  //   Point: point type, should model point concept.
  //   Segment: segment type, should model segment concept.
  //
  // Important:
  //   discretization should contain both edge endpoints initially.
  template <class InCT1, class InCT2,
            template<class> class Point,
            template<class> class Segment>
  static
  typename enable_if<
    typename gtl_and<
      typename gtl_if<
        typename is_point_concept<
          typename geometry_concept< Point<InCT1> >::type
        >::type
      >::type,
      typename gtl_if<
        typename is_segment_concept<
          typename geometry_concept< Segment<InCT2> >::type
        >::type
      >::type
    >::type,
    void
  >::type discretize(
      const Point<InCT1>& point,
      const Segment<InCT2>& segment,
      const CT max_dist,
      std::vector< Point<CT> >* discretization) {
    // Apply the linear transformation to move start point of the segment to
    // the point with coordinates (0, 0) and the direction of the segment to
    // coincide the positive direction of the x-axis.
    CT segm_vec_x = cast(x(high(segment))) - cast(x(low(segment)));
    CT segm_vec_y = cast(y(high(segment))) - cast(y(low(segment)));
    CT sqr_segment_length = segm_vec_x * segm_vec_x + segm_vec_y * segm_vec_y;

    // Compute x-coordinates of the endpoints of the edge
    // in the transformed space.
    CT projection_start = sqr_segment_length *
        get_point_projection((*discretization)[0], segment);
    CT projection_end = sqr_segment_length *
        get_point_projection((*discretization)[1], segment);

    // Compute parabola parameters in the transformed space.
    // Parabola has next representation:
    // f(x) = ((x-rot_x)^2 + rot_y^2) / (2.0*rot_y).
    CT point_vec_x = cast(x(point)) - cast(x(low(segment)));
    CT point_vec_y = cast(y(point)) - cast(y(low(segment)));
    CT rot_x = segm_vec_x * point_vec_x + segm_vec_y * point_vec_y;
    CT rot_y = segm_vec_x * point_vec_y - segm_vec_y * point_vec_x;

    // Save the last point.
    Point<CT> last_point = (*discretization)[1];
    discretization->pop_back();

    // Use stack to avoid recursion.
    std::stack<CT> point_stack;
    point_stack.push(projection_end);
    CT cur_x = projection_start;
    CT cur_y = parabola_y(cur_x, rot_x, rot_y);

    // Adjust max_dist parameter in the transformed space.
    const CT max_dist_transformed = max_dist * max_dist * sqr_segment_length;
    while (!point_stack.empty()) {
      CT new_x = point_stack.top();
      CT new_y = parabola_y(new_x, rot_x, rot_y);

      // Compute coordinates of the point of the parabola that is
      // furthest from the current line segment.
      CT mid_x = (new_y - cur_y) / (new_x - cur_x) * rot_y + rot_x;
      CT mid_y = parabola_y(mid_x, rot_x, rot_y);

      // Compute maximum distance between the given parabolic arc
      // and line segment that discretize it.
      CT dist = (new_y - cur_y) * (mid_x - cur_x) -
          (new_x - cur_x) * (mid_y - cur_y);
      dist = dist * dist / ((new_y - cur_y) * (new_y - cur_y) +
          (new_x - cur_x) * (new_x - cur_x));
      if (dist <= max_dist_transformed) {
        // Distance between parabola and line segment is less than max_dist.
        point_stack.pop();
        CT inter_x = (segm_vec_x * new_x - segm_vec_y * new_y) /
            sqr_segment_length + cast(x(low(segment)));
        CT inter_y = (segm_vec_x * new_y + segm_vec_y * new_x) /
            sqr_segment_length + cast(y(low(segment)));
        discretization->push_back(Point<CT>(inter_x, inter_y));
        cur_x = new_x;
        cur_y = new_y;
      } else {
        point_stack.push(mid_x);
      }
    }

    // Update last point.
    discretization->back() = last_point;
  }

 private:
  // Compute y(x) = ((x - a) * (x - a) + b * b) / (2 * b).
  static CT parabola_y(CT x, CT a, CT b) {
    return ((x - a) * (x - a) + b * b) / (b + b);
  }

  // Get normalized length of the distance between:
  //   1) point projection onto the segment
  //   2) start point of the segment
  // Return this length divided by the segment length. This is made to avoid
  // sqrt computation during transformation from the initial space to the
  // transformed one and vice versa. The assumption is made that projection of
  // the point lies between the start-point and endpoint of the segment.
  template <class InCT,
            template<class> class Point,
            template<class> class Segment>
  static
  typename enable_if<
    typename gtl_and<
      typename gtl_if<
        typename is_point_concept<
          typename geometry_concept< Point<int> >::type
        >::type
      >::type,
      typename gtl_if<
        typename is_segment_concept<
          typename geometry_concept< Segment<long> >::type
        >::type
      >::type
    >::type,
    CT
  >::type get_point_projection(
      const Point<CT>& point, const Segment<InCT>& segment) {
    CT segment_vec_x = cast(x(high(segment))) - cast(x(low(segment)));
    CT segment_vec_y = cast(y(high(segment))) - cast(y(low(segment)));
    CT point_vec_x = x(point) - cast(x(low(segment)));
    CT point_vec_y = y(point) - cast(y(low(segment)));
    CT sqr_segment_length =
        segment_vec_x * segment_vec_x + segment_vec_y * segment_vec_y;
    CT vec_dot = segment_vec_x * point_vec_x + segment_vec_y * point_vec_y;
    return vec_dot / sqr_segment_length;
  }

  template <typename InCT>
  static CT cast(const InCT& value) {
    return static_cast<CT>(value);
  }
};

} } // namespace boost::polygon
#endif

using namespace boost::polygon;  // provides also high() and low()

namespace Slic3r { namespace Geometry {

static bool
sort_points (Point a, Point b)
{
    return (a.x < b.x) || (a.x == b.x && a.y < b.y);
}

/* This implementation is based on Andrew's monotone chain 2D convex hull algorithm */
Polygon
convex_hull(Points points)
{
    assert(points.size() >= 3);
    // sort input points
    std::sort(points.begin(), points.end(), sort_points);
    
    int n = points.size(), k = 0;
    Polygon hull;
    hull.points.resize(2*n);

    // Build lower hull
    for (int i = 0; i < n; i++) {
        while (k >= 2 && points[i].ccw(hull.points[k-2], hull.points[k-1]) <= 0) k--;
        hull.points[k++] = points[i];
    }

    // Build upper hull
    for (int i = n-2, t = k+1; i >= 0; i--) {
        while (k >= t && points[i].ccw(hull.points[k-2], hull.points[k-1]) <= 0) k--;
        hull.points[k++] = points[i];
    }

    hull.points.resize(k);
    
    assert( hull.points.front().coincides_with(hull.points.back()) );
    hull.points.pop_back();
    
    return hull;
}

Polygon
convex_hull(const Polygons &polygons)
{
    Points pp;
    for (Polygons::const_iterator p = polygons.begin(); p != polygons.end(); ++p) {
        pp.insert(pp.end(), p->points.begin(), p->points.end());
    }
    return convex_hull(pp);
}

/* accepts an arrayref of points and returns a list of indices
   according to a nearest-neighbor walk */
void
chained_path(const Points &points, std::vector<Points::size_type> &retval, Point start_near)
{
    PointConstPtrs my_points;
    std::map<const Point*,Points::size_type> indices;
    my_points.reserve(points.size());
    for (Points::const_iterator it = points.begin(); it != points.end(); ++it) {
        my_points.push_back(&*it);
        indices[&*it] = it - points.begin();
    }
    
    retval.reserve(points.size());
    while (!my_points.empty()) {
        Points::size_type idx = start_near.nearest_point_index(my_points);
        start_near = *my_points[idx];
        retval.push_back(indices[ my_points[idx] ]);
        my_points.erase(my_points.begin() + idx);
    }
}

void
chained_path(const Points &points, std::vector<Points::size_type> &retval)
{
    if (points.empty()) return;  // can't call front() on empty vector
    chained_path(points, retval, points.front());
}

/* retval and items must be different containers */
template<class T>
void
chained_path_items(Points &points, T &items, T &retval)
{
    std::vector<Points::size_type> indices;
    chained_path(points, indices);
    for (std::vector<Points::size_type>::const_iterator it = indices.begin(); it != indices.end(); ++it)
        retval.push_back(items[*it]);
}
template void chained_path_items(Points &points, ClipperLib::PolyNodes &items, ClipperLib::PolyNodes &retval);

bool
directions_parallel(double angle1, double angle2, double max_diff)
{
    double diff = fabs(angle1 - angle2);
    max_diff += EPSILON;
    return diff < max_diff || fabs(diff - PI) < max_diff;
}

template<class T>
bool
contains(const std::vector<T> &vector, const Point &point)
{
    for (typename std::vector<T>::const_iterator it = vector.begin(); it != vector.end(); ++it) {
        if (it->contains(point)) return true;
    }
    return false;
}
template bool contains(const ExPolygons &vector, const Point &point);

double
rad2deg(double angle)
{
    return angle / PI * 180.0;
}

double
rad2deg_dir(double angle)
{
    angle = (angle < PI) ? (-angle + PI/2.0) : (angle + PI/2.0);
    if (angle < 0) angle += PI;
    return rad2deg(angle);
}

double
deg2rad(double angle)
{
    return PI * angle / 180.0;
}

void
simplify_polygons(const Polygons &polygons, double tolerance, Polygons* retval)
{
    Polygons pp;
    for (Polygons::const_iterator it = polygons.begin(); it != polygons.end(); ++it) {
        Polygon p = *it;
        p.points.push_back(p.points.front());
        p.points = MultiPoint::_douglas_peucker(p.points, tolerance);
        p.points.pop_back();
        pp.push_back(p);
    }
    Slic3r::simplify_polygons(pp, retval);
}

double
linint(double value, double oldmin, double oldmax, double newmin, double newmax)
{
    return (value - oldmin) * (newmax - newmin) / (oldmax - oldmin) + newmin;
}

Pointfs
arrange(size_t total_parts, Pointf part, coordf_t dist, const BoundingBoxf* bb)
{
    // use actual part size (the largest) plus separation distance (half on each side) in spacing algorithm
    part.x += dist;
    part.y += dist;
    
    Pointf area;
    if (bb != NULL && bb->defined) {
        area = bb->size();
    } else {
        // bogus area size, large enough not to trigger the error below
        area.x = part.x * total_parts;
        area.y = part.y * total_parts;
    }
    
    // this is how many cells we have available into which to put parts
    size_t cellw = floor((area.x + dist) / part.x);
    size_t cellh = floor((area.y + dist) / part.y);
    if (total_parts > (cellw * cellh))
        CONFESS("%zu parts won't fit in your print area!\n", total_parts);
    
    // total space used by cells
    Pointf cells(cellw * part.x, cellh * part.y);
    
    // bounding box of total space used by cells
    BoundingBoxf cells_bb;
    cells_bb.merge(Pointf(0,0)); // min
    cells_bb.merge(cells);  // max
    
    // center bounding box to area
    cells_bb.translate(
        (area.x - cells.x) / 2,
        (area.y - cells.y) / 2
    );
    
    // list of cells, sorted by distance from center
    std::vector<ArrangeItemIndex> cellsorder;
    
    // work out distance for all cells, sort into list
    for (size_t i = 0; i <= cellw-1; ++i) {
        for (size_t j = 0; j <= cellh-1; ++j) {
            coordf_t cx = linint(i + 0.5, 0, cellw, cells_bb.min.x, cells_bb.max.x);
            coordf_t cy = linint(j + 0.5, 0, cellh, cells_bb.min.y, cells_bb.max.y);
            
            coordf_t xd = fabs((area.x / 2) - cx);
            coordf_t yd = fabs((area.y / 2) - cy);
            
            ArrangeItem c;
            c.pos.x = cx;
            c.pos.y = cy;
            c.index_x = i;
            c.index_y = j;
            c.dist = xd * xd + yd * yd - fabs((cellw / 2) - (i + 0.5));
            
            // binary insertion sort
            {
                coordf_t index = c.dist;
                size_t low = 0;
                size_t high = cellsorder.size();
                while (low < high) {
                    size_t mid = (low + ((high - low) / 2)) | 0;
                    coordf_t midval = cellsorder[mid].index;
                    
                    if (midval < index) {
                        low = mid + 1;
                    } else if (midval > index) {
                        high = mid;
                    } else {
                        cellsorder.insert(cellsorder.begin() + mid, ArrangeItemIndex(index, c));
                        goto ENDSORT;
                    }
                }
                cellsorder.insert(cellsorder.begin() + low, ArrangeItemIndex(index, c));
            }
            ENDSORT: true;
        }
    }
    
    // the extents of cells actually used by objects
    coordf_t lx = 0;
    coordf_t ty = 0;
    coordf_t rx = 0;
    coordf_t by = 0;

    // now find cells actually used by objects, map out the extents so we can position correctly
    for (size_t i = 1; i <= total_parts; ++i) {
        ArrangeItemIndex c = cellsorder[i - 1];
        coordf_t cx = c.item.index_x;
        coordf_t cy = c.item.index_y;
        if (i == 1) {
            lx = rx = cx;
            ty = by = cy;
        } else {
            if (cx > rx) rx = cx;
            if (cx < lx) lx = cx;
            if (cy > by) by = cy;
            if (cy < ty) ty = cy;
        }
    }
    // now we actually place objects into cells, positioned such that the left and bottom borders are at 0
    Pointfs positions;
    for (size_t i = 1; i <= total_parts; ++i) {
        ArrangeItemIndex c = cellsorder.front();
        cellsorder.erase(cellsorder.begin());
        coordf_t cx = c.item.index_x - lx;
        coordf_t cy = c.item.index_y - ty;
        
        positions.push_back(Pointf(cx * part.x, cy * part.y));
    }
    
    if (bb != NULL && bb->defined) {
        for (Pointfs::iterator p = positions.begin(); p != positions.end(); ++p) {
            p->x += bb->min.x;
            p->y += bb->min.y;
        }
    }
    
    return positions;
}

Line
MedialAxis::edge_to_line(const VD::edge_type &edge) const
{
    Line line;
    line.a.x = edge.vertex0()->x();
    line.a.y = edge.vertex0()->y();
    line.b.x = edge.vertex1()->x();
    line.b.y = edge.vertex1()->y();
    return line;
}

#ifdef SLIC3R_DEBUG
// The following code for the visualization of the boost Voronoi diagram is based on:
//
// Boost.Polygon library voronoi_visualizer.cpp file
//          Copyright Andrii Sydorchuk 2010-2012.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)
namespace Voronoi { namespace Internal {

    typedef double coordinate_type;
    typedef boost::polygon::point_data<coordinate_type> point_type;
    typedef boost::polygon::segment_data<coordinate_type> segment_type;
    typedef boost::polygon::rectangle_data<coordinate_type> rect_type;
//    typedef voronoi_builder<int> VB;
    typedef boost::polygon::voronoi_diagram<coordinate_type> VD;
    typedef VD::cell_type cell_type;
    typedef VD::cell_type::source_index_type source_index_type;
    typedef VD::cell_type::source_category_type source_category_type;
    typedef VD::edge_type edge_type;
    typedef VD::cell_container_type cell_container_type;
    typedef VD::cell_container_type vertex_container_type;
    typedef VD::edge_container_type edge_container_type;
    typedef VD::const_cell_iterator const_cell_iterator;
    typedef VD::const_vertex_iterator const_vertex_iterator;
    typedef VD::const_edge_iterator const_edge_iterator;

    static const std::size_t EXTERNAL_COLOR = 1;

    inline void color_exterior(const VD::edge_type* edge) 
    {
        if (edge->color() == EXTERNAL_COLOR)
            return;
        edge->color(EXTERNAL_COLOR);
        edge->twin()->color(EXTERNAL_COLOR);
        const VD::vertex_type* v = edge->vertex1();
        if (v == NULL || !edge->is_primary())
            return;
        v->color(EXTERNAL_COLOR);
        const VD::edge_type* e = v->incident_edge();
        do {
            color_exterior(e);
            e = e->rot_next();
        } while (e != v->incident_edge());
    }

    inline point_type retrieve_point(const std::vector<segment_type> &segments, const cell_type& cell) 
    {
        assert(cell.source_category() == SOURCE_CATEGORY_SEGMENT_START_POINT || cell.source_category() == SOURCE_CATEGORY_SEGMENT_END_POINT);
        return (cell.source_category() == SOURCE_CATEGORY_SEGMENT_START_POINT) ? low(segments[cell.source_index()]) : high(segments[cell.source_index()]);
    }

    inline void clip_infinite_edge(const std::vector<segment_type> &segments, const edge_type& edge, coordinate_type bbox_max_size, std::vector<point_type>* clipped_edge) 
    {
        const cell_type& cell1 = *edge.cell();
        const cell_type& cell2 = *edge.twin()->cell();
        point_type origin, direction;
        // Infinite edges could not be created by two segment sites.
        if (cell1.contains_point() && cell2.contains_point()) {
            point_type p1 = retrieve_point(segments, cell1);
            point_type p2 = retrieve_point(segments, cell2);
            origin.x((p1.x() + p2.x()) * 0.5);
            origin.y((p1.y() + p2.y()) * 0.5);
            direction.x(p1.y() - p2.y());
            direction.y(p2.x() - p1.x());
        } else {
            origin = cell1.contains_segment() ? retrieve_point(segments, cell2) : retrieve_point(segments, cell1);
            segment_type segment = cell1.contains_segment() ? segments[cell1.source_index()] : segments[cell2.source_index()];
            coordinate_type dx = high(segment).x() - low(segment).x();
            coordinate_type dy = high(segment).y() - low(segment).y();
            if ((low(segment) == origin) ^ cell1.contains_point()) {
                direction.x(dy);
                direction.y(-dx);
            } else {
                direction.x(-dy);
                direction.y(dx);
            }
        }
        coordinate_type koef = bbox_max_size / (std::max)(fabs(direction.x()), fabs(direction.y()));
        if (edge.vertex0() == NULL) {
            clipped_edge->push_back(point_type(
                origin.x() - direction.x() * koef,
                origin.y() - direction.y() * koef));
        } else {
            clipped_edge->push_back(
                point_type(edge.vertex0()->x(), edge.vertex0()->y()));
        }
        if (edge.vertex1() == NULL) {
            clipped_edge->push_back(point_type(
                origin.x() + direction.x() * koef,
                origin.y() + direction.y() * koef));
        } else {
            clipped_edge->push_back(
                point_type(edge.vertex1()->x(), edge.vertex1()->y()));
        }
    }

    inline void sample_curved_edge(const std::vector<segment_type> &segments, const edge_type& edge, std::vector<point_type> &sampled_edge, coordinate_type max_dist) 
    {
        point_type point = edge.cell()->contains_point() ?
            retrieve_point(segments, *edge.cell()) :
            retrieve_point(segments, *edge.twin()->cell());
        segment_type segment = edge.cell()->contains_point() ?
            segments[edge.twin()->cell()->source_index()] :
            segments[edge.cell()->source_index()];
        ::boost::polygon::voronoi_visual_utils<coordinate_type>::discretize(point, segment, max_dist, &sampled_edge);
    }

} /* namespace Internal */ } // namespace Voronoi

static inline void dump_voronoi_to_svg(const Lines &lines, /* const */ voronoi_diagram<double> &vd, const Polylines *polylines, const char *path)
{
    const double        scale                       = 0.2;
    const std::string   inputSegmentPointColor      = "lightseagreen";
    const coord_t       inputSegmentPointRadius     = coord_t(0.09 * scale / SCALING_FACTOR); 
    const std::string   inputSegmentColor           = "lightseagreen";
    const coord_t       inputSegmentLineWidth       = coord_t(0.03 * scale / SCALING_FACTOR);

    const std::string   voronoiPointColor           = "black";
    const coord_t       voronoiPointRadius          = coord_t(0.06 * scale / SCALING_FACTOR);
    const std::string   voronoiLineColorPrimary     = "black";
    const std::string   voronoiLineColorSecondary   = "green";
    const std::string   voronoiArcColor             = "red";
    const coord_t       voronoiLineWidth            = coord_t(0.02 * scale / SCALING_FACTOR);

    const bool          internalEdgesOnly           = false;
    const bool          primaryEdgesOnly            = false;

    BoundingBox bbox = BoundingBox(lines);
    bbox.min.x -= coord_t(1. / SCALING_FACTOR);
    bbox.min.y -= coord_t(1. / SCALING_FACTOR);
    bbox.max.x += coord_t(1. / SCALING_FACTOR);
    bbox.max.y += coord_t(1. / SCALING_FACTOR);

    ::Slic3r::SVG svg(path, bbox);

//    bbox.scale(1.2);
    // For clipping of half-lines to some reasonable value.
    // The line will then be clipped by the SVG viewer anyway.
    const double bbox_dim_max = double(bbox.max.x - bbox.min.x) + double(bbox.max.y - bbox.min.y);
    // For the discretization of the Voronoi parabolic segments.
    const double discretization_step = 0.0005 * bbox_dim_max;

    // Make a copy of the input segments with the double type.
    std::vector<Voronoi::Internal::segment_type> segments;
    for (Lines::const_iterator it = lines.begin(); it != lines.end(); ++ it)
        segments.push_back(Voronoi::Internal::segment_type(
            Voronoi::Internal::point_type(double(it->a.x), double(it->a.y)), 
            Voronoi::Internal::point_type(double(it->b.x), double(it->b.y))));
    
    // Color exterior edges.
    for (voronoi_diagram<double>::const_edge_iterator it = vd.edges().begin(); it != vd.edges().end(); ++it)
        if (!it->is_finite())
            Voronoi::Internal::color_exterior(&(*it));

    // Draw the end points of the input polygon.
    for (Lines::const_iterator it = lines.begin(); it != lines.end(); ++it) {
        svg.draw(it->a, inputSegmentPointColor, inputSegmentPointRadius);
        svg.draw(it->b, inputSegmentPointColor, inputSegmentPointRadius);
    }
    // Draw the input polygon.
    for (Lines::const_iterator it = lines.begin(); it != lines.end(); ++it)
        svg.draw(Line(Point(coord_t(it->a.x), coord_t(it->a.y)), Point(coord_t(it->b.x), coord_t(it->b.y))), inputSegmentColor, inputSegmentLineWidth);

#if 1
    // Draw voronoi vertices.
    for (voronoi_diagram<double>::const_vertex_iterator it = vd.vertices().begin(); it != vd.vertices().end(); ++it)
        if (! internalEdgesOnly || it->color() != Voronoi::Internal::EXTERNAL_COLOR)
            svg.draw(Point(coord_t(it->x()), coord_t(it->y())), voronoiPointColor, voronoiPointRadius);

    for (voronoi_diagram<double>::const_edge_iterator it = vd.edges().begin(); it != vd.edges().end(); ++it) {
        if (primaryEdgesOnly && !it->is_primary())
            continue;
        if (internalEdgesOnly && (it->color() == Voronoi::Internal::EXTERNAL_COLOR))
            continue;
        std::vector<Voronoi::Internal::point_type> samples;
        std::string color = voronoiLineColorPrimary;
        if (!it->is_finite()) {
            Voronoi::Internal::clip_infinite_edge(segments, *it, bbox_dim_max, &samples);
            if (! it->is_primary())
                color = voronoiLineColorSecondary;
        } else {
            // Store both points of the segment into samples. sample_curved_edge will split the initial line
            // until the discretization_step is reached.
            samples.push_back(Voronoi::Internal::point_type(it->vertex0()->x(), it->vertex0()->y()));
            samples.push_back(Voronoi::Internal::point_type(it->vertex1()->x(), it->vertex1()->y()));
            if (it->is_curved()) {
                Voronoi::Internal::sample_curved_edge(segments, *it, samples, discretization_step);
                color = voronoiArcColor;
            } else if (! it->is_primary())
                color = voronoiLineColorSecondary;
        }
        for (std::size_t i = 0; i + 1 < samples.size(); ++i)
            svg.draw(Line(Point(coord_t(samples[i].x()), coord_t(samples[i].y())), Point(coord_t(samples[i+1].x()), coord_t(samples[i+1].y()))), color, voronoiLineWidth);
    }
#endif

    if (polylines != NULL) {
        svg.draw(*polylines, "blue", voronoiLineWidth);
    }

    svg.Close();
}
#endif /* SLIC3R_DEBUG */

void
MedialAxis::build(Polylines* polylines)
{
    /*
    // build bounding box (we use it for clipping infinite segments)
    // --> we have no infinite segments
    this->bb = BoundingBox(this->lines);
    */

    construct_voronoi(this->lines.begin(), this->lines.end(), &this->vd);
    
    /*
    // DEBUG: dump all Voronoi edges
    {
        for (VD::const_edge_iterator edge = this->vd.edges().begin(); edge != this->vd.edges().end(); ++edge) {
            if (edge->is_infinite()) continue;
            
            Polyline polyline;
            polyline.points.push_back(Point( edge->vertex0()->x(), edge->vertex0()->y() ));
            polyline.points.push_back(Point( edge->vertex1()->x(), edge->vertex1()->y() ));
            polylines->push_back(polyline);
        }
        return;
    }
    */
    
    typedef const VD::vertex_type vert_t;
    typedef const VD::edge_type   edge_t;
    
    // collect valid edges (i.e. prune those not belonging to MAT)
    // note: this keeps twins, so it inserts twice the number of the valid edges
    this->edges.clear();
    for (VD::const_edge_iterator edge = this->vd.edges().begin(); edge != this->vd.edges().end(); ++edge) {
        // if we only process segments representing closed loops, none if the
        // infinite edges (if any) would be part of our MAT anyway
        if (edge->is_secondary() || edge->is_infinite()) continue;
        this->edges.insert(&*edge);
    }
    
    // count valid segments for each vertex
    std::map< vert_t*,std::set<edge_t*> > vertex_edges;  // collects edges connected for each vertex
    std::set<vert_t*> startpoints;                       // collects all vertices having a single starting edge
    for (VD::const_vertex_iterator it = this->vd.vertices().begin(); it != this->vd.vertices().end(); ++it) {
        vert_t* vertex = &*it;
        
        // loop through all edges originating from this vertex
        // starting from a random one
        edge_t* edge = vertex->incident_edge();
        do {
            // if this edge was not pruned by our filter above,
            // add it to vertex_edges
            if (this->edges.count(edge) > 0)
                vertex_edges[vertex].insert(edge);
            
            // continue looping next edge originating from this vertex
            edge = edge->rot_next();
        } while (edge != vertex->incident_edge());
        
        // if there's only one edge starting at this vertex then it's an endpoint
        if (vertex_edges[vertex].size() == 1) {
            startpoints.insert(vertex);
        }
    }
    
    // prune startpoints recursively if extreme segments are not valid
    while (!startpoints.empty()) {
        // get a random entry node
        vert_t* v = *startpoints.begin();
    
        // get edge starting from v
        assert(vertex_edges[v].size() == 1);
        edge_t* edge = *vertex_edges[v].begin();
        
        if (!this->is_valid_edge(*edge)) {
            // if edge is not valid, erase it and its twin from edge list
            (void)this->edges.erase(edge);
            (void)this->edges.erase(edge->twin());
            
            // decrement edge counters for the affected nodes
            vert_t* v1 = edge->vertex1();
            (void)vertex_edges[v].erase(edge);
            (void)vertex_edges[v1].erase(edge->twin());
            
            // also, check whether the end vertex is a new leaf
            if (vertex_edges[v1].size() == 1) {
                startpoints.insert(v1);
            } else if (vertex_edges[v1].empty()) {
                startpoints.erase(v1);
            }
        }
        
        // remove node from the set to prevent it from being visited again
        startpoints.erase(v);
    }
    
    // iterate through the valid edges to build polylines
    while (!this->edges.empty()) {
        edge_t &edge = **this->edges.begin();
        
        // start a polyline
        Polyline polyline;
        polyline.points.push_back(Point( edge.vertex0()->x(), edge.vertex0()->y() ));
        polyline.points.push_back(Point( edge.vertex1()->x(), edge.vertex1()->y() ));
        
        // remove this edge and its twin from the available edges
        (void)this->edges.erase(&edge);
        (void)this->edges.erase(edge.twin());
        
        // get next points
        this->process_edge_neighbors(edge, &polyline.points);
        
        // get previous points
        {
            Points pp;
            this->process_edge_neighbors(*edge.twin(), &pp);
            polyline.points.insert(polyline.points.begin(), pp.rbegin(), pp.rend());
        }
        
        // append polyline to result
        polylines->push_back(polyline);
    }

    #ifdef SLIC3R_DEBUG
    {
        char path[2048];
        static int iRun = 0;
        sprintf(path, "out/MedialAxis-%d.svg", iRun ++);
        dump_voronoi_to_svg(this->lines, this->vd, polylines, path);
    }
    #endif /* SLIC3R_DEBUG */
}

void
MedialAxis::process_edge_neighbors(const VD::edge_type& edge, Points* points)
{
    // Since rot_next() works on the edge starting point but we want
    // to find neighbors on the ending point, we just swap edge with
    // its twin.
    const VD::edge_type& twin = *edge.twin();
    
    // count neighbors for this edge
    std::vector<const VD::edge_type*> neighbors;
    for (const VD::edge_type* neighbor = twin.rot_next(); neighbor != &twin; neighbor = neighbor->rot_next()) {
        if (this->edges.count(neighbor) > 0) neighbors.push_back(neighbor);
    }
    
    // if we have a single neighbor then we can continue recursively
    if (neighbors.size() == 1) {
        const VD::edge_type& neighbor = *neighbors.front();
        points->push_back(Point( neighbor.vertex1()->x(), neighbor.vertex1()->y() ));
        (void)this->edges.erase(&neighbor);
        (void)this->edges.erase(neighbor.twin());
        this->process_edge_neighbors(neighbor, points);
    }
}

bool
MedialAxis::is_valid_edge(const VD::edge_type& edge) const
{
    /* If the cells sharing this edge have a common vertex, we're not interested
       in this edge. Why? Because it means that the edge lies on the bisector of
       two contiguous input lines and it was included in the Voronoi graph because
       it's the locus of centers of circles tangent to both vertices. Due to the 
       "thin" nature of our input, these edges will be very short and not part of
       our wanted output. */
    
    // retrieve the original line segments which generated the edge we're checking
    const VD::cell_type &cell1 = *edge.cell();
    const VD::cell_type &cell2 = *edge.twin()->cell();
    if (!cell1.contains_segment() || !cell2.contains_segment()) return false;
    const Line &segment1 = this->lines[cell1.source_index()];
    const Line &segment2 = this->lines[cell2.source_index()];
    
    // calculate the relative angle between the two boundary segments
    double angle = fabs(segment2.orientation() - segment1.orientation());
    
    // fabs(angle) ranges from 0 (collinear, same direction) to PI (collinear, opposite direction)
    // we're interested only in segments close to the second case (facing segments)
    // so we allow some tolerance.
    // this filter ensures that we're dealing with a narrow/oriented area (longer than thick)
    if (fabs(angle - PI) > PI/5) {
        return false;
    }
    
    // each edge vertex is equidistant to both cell segments
    // but such distance might differ between the two vertices;
    // in this case it means the shape is getting narrow (like a corner)
    // and we might need to skip the edge since it's not really part of
    // our skeleton
    
    // get perpendicular distance of each edge vertex to the segment(s)
    double dist0 = segment1.a.distance_to(segment2.b);
    double dist1 = segment1.b.distance_to(segment2.a);
    
    /*
    Line line = this->edge_to_line(edge);
    double diff = fabs(dist1 - dist0);
    double dist_between_segments1 = segment1.a.distance_to(segment2);
    double dist_between_segments2 = segment1.b.distance_to(segment2);
    printf("w = %f/%f, dist0 = %f, dist1 = %f, diff = %f, seg1len = %f, seg2len = %f, edgelen = %f, s2s = %f / %f\n",
        unscale(this->max_width), unscale(this->min_width),
        unscale(dist0), unscale(dist1), unscale(diff),
        unscale(segment1.length()), unscale(segment2.length()),
        unscale(line.length()),
        unscale(dist_between_segments1), unscale(dist_between_segments2)
        );
    */

    // if this edge is the centerline for a very thin area, we might want to skip it
    // in case the area is too thin
    if (dist0 < this->min_width && dist1 < this->min_width) {
        //printf(" => too thin, skipping\n");
        return false;
    }
    
    return true;
}

// Calculate an area of a CCW oriented triangle.
template<typename VD>
inline typename VD::coord_type area(typename VD::point_type &p1, typename VD::point_type &p2, typename VD::point_type &p3)
{
    typedef typename VD::coord_type T;
    T x1 = p2.x - p1.x;
    T y1 = p2.y - p1.y;
    T x2 = p3.x - p2.x;
    T y2 = p3.y - p2.y;
    T a  = T(0.5) * (x1 * y2 - x2 * y1);
    // The triangle has to be oriented counter-clockwise for its area to be positive.
    assert(a >= T(0.);
    return a;
}

// Calculate an area of a CCW oriented trapezoid.
template<typename VD>
inline typename VD::coord_type area(typename VD::point_type &p1, typename VD::point_type &p2, typename VD::point_type &p3, typename VD::point_type &p4)
{
    return area(p1, p2, p3) + area(p1, p3, p4);
}

// Find a foot point of "px" on a segment "seg".
template<typename VD>
inline typename VD::point_type project_point_to_segment(typename VD::segment_type &seg, typename VD::point_type &px)
{
    typedef typename VD::coord_type T;
    const typename VD::point_type &p0 = low(seg);
    const typename VD::point_type &p1 = high(seg);
    const typename VD::point_type  dir(p1.x-p0.x, p1.y-p0.y);
    const typename VD::point_type  dproj(px.x-p0.x, px.y-p0.y);
    const typename VD::coord_type  t = (dir.x * dproj.x + dir.y * dproj.y) / (dir.x * dir.x + dir.y * dir.y);
    assert(t >= T(-1e-6) && t <= T(1. + 1e-6);
    return typename VD::point_type(p0.x + t * p1.x, p0.y + t * p1.y);
}

template<typename VD, typename SEGMENTS>
inline typename const VD::point_type& retrieve_point(const SEGMENTS &segments, const typename VD::cell_type& cell)
{
    assert(cell.source_category() == SOURCE_CATEGORY_SEGMENT_START_POINT || cell.source_category() == SOURCE_CATEGORY_SEGMENT_END_POINT);
    return (cell.source_category() == SOURCE_CATEGORY_SEGMENT_START_POINT) ? low(segments[cell.source_index()]) : high(segments[cell.source_index()]);
}

// Evaluate area of the left & right Voronoi cells spanned by a segment of the medial axis.
template<typename VD, typename SEGMENTS>
inline double area(typename VD::edge_type *edge, const SEGMENTS &segments)
{
    typename const VD::point_type  pa(edge->vertex1()->x(), edge->vertex1()->y());
    typename const VD::point_type  pb(edge->vertex2()->x(), edge->vertex2()->y());
    const typename VD::cell_type  &cell1 = *edge.cell();
    const typename VD::cell_type  &cell2 = *edge.twin()->cell();
    if (cell1.contains_segment()) {
        if (cell2.contains_segment()) {
            // Both cells contain a linear segment, the left / right cells are symmetric.
            // Project pa, pb to the left segment.
            const tupename VD::segment_type &segment1 = segments[cell1.source_index()];
            typename const VD::point_type p1a = project_point_to_segment(segment1, pa);
            typename const VD::point_type p1b = project_point_to_segment(segment1, pb);
            return T(2.) * area(p1a, p1b, pb, pa);
        } else {
            // 1st cell contains a linear segment, 2nd cell contains a point.
            // The medial axis between the cells is a parabolic arc.
            // Project pa, pb to the left segment.
            const tupename VD::segment_type &segment1 = segments[cell1.source_index()];
            return
                area(project_point_to_segment(segment1, pa), 
                     project_point_to_segment(segment1, pb), 
                     pb, pa) + 
                area(pa, pb, retrieve_point(segments, cell2));
        }
    } else if (cell2.contains_segment()) {
        // 1st cell contains a point, 2nd cell contains a linear segment.
        // The medial axis between the cells is a parabolic arc.
        const tupename VD::segment_type &segment2 = segments[cell2.source_index()];
        return
            area(pa, pb, retrieve_point(segments, cell2)) +
            area(pa, pb,
                 project_point_to_segment(segment2, pb), 
                 project_point_to_segment(segment2, pa));
    } else {
        // Both cells contain a point. The left / right regions are triangular and symmetric.
        return T(2.) * area(pa, pb, retrieve_point(segments, cell2));
    }
}

// Converts the Line instances of Lines vector to VD::segment_type.
template<typename VD>
class Lines2VDSegments
{
public:
    Lines2VDSegments(const Lines &alines) : lines(alines) {}
    typename VD::segment_type operator[](size_t idx) const {
        typename VD::segment_type(
            typename VD::point_type(typename VD::coord_type(it->a.x), typename VD::coord_type(it->a.y)),
            typename VD::point_type(typename VD::coord_type(it->b.x), typename VD::coord_type(it->b.y)));
    }
private:
    const Lines &lines;
};

// New boost::Graph properties for mapping of the simplified graph onto the inner Voronoi edges
// of the boost::Polygon Voronoi diagram.
namespace boost {
    enum vertex2vd_t { vertex2vd };
    enum edge2vd_t   { edge2vd };
    BOOST_INSTALL_PROPERTY(vertex, vertex2vd);
    BOOST_INSTALL_PROPERTY(edge, edge2vd);
}

void MedialAxis2::build(Polylines* polylines)
{
    // 1) Create a Voronoi diagram of points and linear segments using the Boost::Polygon library.
    construct_voronoi(this->lines.begin(), this->lines.end(), &this->vd);

    // 2) Create a graph of the single connected segments and their branches.
    // This compresses non-branching sequences of segments into a single segment.
    // The segments in the new graph will be weighted by the area they span.

    // Store a pointer to the Voronoi vertex in the graph.
    typedef property<vertex2vd_t, VD::vertex_type*, 
            property<vertex_degree_t, size_t> > VertexProperty;
    typedef property<edge2vd_t, VD::edge_type*,
            property<edge_weight_t, double> > EdgeProperty;
    typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::undirectedS, VertexProperty, EdgeProperty> Graph;
    Graph graph;
    boost::property_map<Graph, boost::vertex2vd_t    >::type vertex_to_vd_vertex = get(boost::vertex2vd_t    (), graph);
    boost::property_map<Graph, boost::vertex_degree_t>::type vertex_degree       = get(boost::vertex_degree_t(), graph);
    boost::property_map<Graph, boost::edge2vd_t      >::type edge_to_vd_edge     = get(boost::edge2vd_t      (), graph);
    boost::property_map<Graph, boost::edge_weight_t  >::type edge_weight         = get(boost::edge_weight_t  (), graph);

    // Traverse the VD edges, set the vertex color to its valency.
    for (VD::vertex_iterator it = this->vd.vertices().begin(); it != this->vd.vertices().end(); ++it)
        it->color(0);
    for (VD::edge_iterator it = this->vd.edges().begin(); it != this->vd.edges().end(); ++it)
        it->vertex1()->color(it->vertex1()->color()+1);

    // Allocate the graph vertices and assign their degrees.
    size_t nVertices = 0;
    for (VD::const_vertex_iterator it = this->vd.vertices().begin(); it != this->vd.vertices().end(); ++it) {
        const VD::vertex_type *vertex = &*it;
        if (vertex->color() == 2) {
            // In the middle of a segment.
            vertex->color(0);
            continue;
        }
        // This is an end of a tree branch or a branching point.
        assert(vertex->color() == 1 || vertex->color() > 2);
        boost::add_vertex(nVertices, graph);
        vertex->color(++ nVertices);
    }

    Lines2VDSegments lines2VDsegments(this->lines);

    // Allocate the graph edges, interconnect the graph vertices,
    // measure the area covered by the segments of the medial axis.
    size_t nEdges = 0;
    for (size_t iv = 0; iv < nVertices; ++ iv) {
        const VD::vertex_type *vertex = boost::get(vertex_color, iv + 1);
        // For all outgoing edges.
        const VD::edge_type *edge   = vertex->incident_edge();
        assert(edge->vertex0 == vertex);
        do {
            // Until a vertex is reached, which has a counterpart in the graph.
            const VD::edge_type *edge2 = edge;
            double a = area(edge, lines2VDsegments);
            while (edge2->vertex1()->color() == 0) {
                edge2 = edge2->next();
                a += area(edge2, lines2VDsegments);
            }
            // Add a new edge into the graph.
            // It is a undirected graph, add an edge only once.
            if (edge2->vertex1()->color() > iv) {
                Graph::edge_descriptor e = boost::add_edge(iv, edge2->vertex1()->color() - 1, graph);
                boost::put(edge_to_vd_edge, edge, graph);
                // Edges are weighted by the negative area they cover,
                // so a search for a shortest path will provide a path, which will extrude the most material.
                boost::put(edge_weight, -a);
                ++ nEdges;
            }
            edge = edge->rot_next();
        } while (edge != vertex->incident_edge());
    }

    // Extract connected components of the graph.
    // In each of the connected components, at most a single extrusion will be produced.
    std::vector<size_t> component(nVertices);
    size_t nComponents = boost::connected_components(graph, &component.front());
    for (size_t iComponent = 0; iComponent < nComponents; ++ iComponent) {
        // Allocate a subgraph for the connected component.
        typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::no_property, property<edge_weight_t, double>> Subgraph;
        Graph subgraph(nVertices2);
        // Count the vertices of this connected component.
        size_t nVertices2 = 0;
        for (size_t iv = 0; iv < nVertices; ++ iv)
            if (component[iv] == iComponent)
                ++ nVertices2;
        // Copy the vertices.
        std::vector<Graph::vertex_descriptor>    mapVertexSubgraph2Graph(nVertices2);
        std::vector<Subgraph::vertex_descriptor> mapVertexGraph2Subgraph(nVertices);
        boost::property_map<Graph, boost::edge_weight_t>::type subgraph_edge_weight = get(boost::edge_weight_t(), subgraph);
        nVertices2 = 0;
        for (size_t iv = 0; iv < nVertices; ++ iv)
            if (component[iv] == iComponent) {
                subgraph.add_vertex();
                mapVertexSubgraph2Graph[nVertices2] = iv;
                mapVertexGraph2Subgraph[iv] = nVertices2;
                ++ nVertices2;
            }
        // Copy the edges with their weights.
        Graph::edge_iterator ei, ei_end;
        size_t nEdges2 = 0;
        for (boost::tie(ei, ei_end) = graph.edges(graph); ei != ei_end; ++ei)
            if (component[source(*ei, graph)] == iComponent && component[target(*ei, graph)] == iComponent)
                ++ nEdges2;
        std::vector<Graph::edge_descriptor>      mapEdgeSubgraph2Graph(nEdges2);
        for (boost::tie(ei, ei_end) = graph.edges(graph); ei != ei_end; ++ei)
            if (component[source(*ei, graph)] == iComponent && component[target(*ei, graph)] == iComponent) {
                Subgraph::edge_descriptor e = subgraph.add_edge(mapVertexGraph2Subgraph[source(*ei, graph)], mapVertexGraph2Sugraph[target(*ei, graph)]);
                subgraph_edge_weight[e] = edge_weight[*ei];
                mapEdgeSubgraph2Graph[e] = *ei;
            }

        // Calculate the distance matrix (the area extruded when following a path)
        // for all pairs of vertices.
        boost::multi_array<double,2> distances(boost::extents[nVertices2][nVertices2]);
        boost::johnson_all_pairs_shortest_paths(subgraph, distances);
    
        // Find the pair of vertices with the shortest distance between them (with the most material extruded).
        size_t iv1, iv2;
        double distMin = std::limits<double>()::max();
        for (size_t r = 0; r < nVertices2; ++ r)
            for (size_t c = r + 1; c < nVertices2; ++ c)
                if (distances[r][c] < distMin) {
                    iv1 = r;
                    iv2 = c;
                    distMin = distances[r][c];
                }

        // Extract the path from iv1 to iv2.
        // Path is indexed in the main graph.
        std::vector<Graph::edge_descriptor> path;
        path.push_back(mapVertexSubgraph2Graph[iv1]);
        while (iv1 != iv2) {
            Graph::out_edge_iterator eit, eend;
            std::tie(eit, eend) = boost::out_edges(iv1, graph);
            T wmin = std::limits<T>()::max();
            Subgraph::edge_edscriptor emin = *eit;
            for (; eit != eend; ++ eit) {
                Subgraph::edge_edscriptor vnext = boost::target(*eit, graph);
                T      w1    = edge_weight[*eit];
                T      w2    = distances[vnext][iv2];
                T      w     = w1 + w2;
                if (w < wmin) {
                    wmin = w;
                    emin = *eit;
                    iv1 = vnext;
                }
            }
            path.push_back(mapEdgeSubgraph2Graph[emin]);
        }

        // 
    }

    #ifdef SLIC3R_DEBUG
    {
        char path[2048];
        static int iRun = 0;
        sprintf(path, "out/MedialAxis-%d.svg", iRun ++);
        dump_voronoi_to_svg(this->lines, this->vd, polylines, path);
    }
    #endif /* SLIC3R_DEBUG */
}

} }
