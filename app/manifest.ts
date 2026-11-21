import type { MetadataRoute } from "next";

// A static export treats this metadata route as a handler. It has to be
// marked static or `next build` refuses to emit manifest.webmanifest.
export const dynamic = "force-static";

export default function manifest(): MetadataRoute.Manifest {
  // Empty locally. GitHub Pages sets PAGES_BASE_PATH, for example /eml-and-one.
  const basePath = process.env.PAGES_BASE_PATH || process.env.BASE_PATH || "";
  const icon = (file: string) => `${basePath}/${file}`;
  return {
    name: "EML and One",
    short_name: "EML and One",
    description: "a two-button calculator",
    start_url: `${basePath}/`,
    scope: `${basePath}/`,
    display: "standalone",
    orientation: "portrait",
    background_color: "#1c2126",
    theme_color: "#343b43",
    icons: [
      { src: icon("icon-192.png"), sizes: "192x192", type: "image/png", purpose: "any" },
      { src: icon("icon-512.png"), sizes: "512x512", type: "image/png", purpose: "any" },
      { src: icon("icon-maskable-512.png"), sizes: "512x512", type: "image/png", purpose: "maskable" },
    ],
  };
}
