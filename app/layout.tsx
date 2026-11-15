import type { Metadata } from "next";
import "./globals.css";

export const metadata: Metadata = {
  applicationName: "EML and One",
  title: "EML and One",
  description: "a two-button calculator",
  openGraph: {
    title: "EML and One",
    description: "a two-button calculator",
    siteName: "EML and One",
  },
};

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
